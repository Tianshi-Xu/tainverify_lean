/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L14FaithfulMoEBranch
import denote.yoco_goals.L12FaithfulMoEExpert
import denote.yoco_goals.L12FaithfulMoEGate
import denote.yoco_goals.L13FaithfulBlockTail

/-!
# Faithful zigzag relations for the block-2 tail (MoE join -> block-3 Q)

Mechanical transport of the (green) block-1 tail `L13FaithfulBlockTail` to
block 2.  The block-2 cu tensor is **5443**.

* SM 597 `FW_all2all_moe_gmm [8240,5458,5459,5461,5462] -> [5463]` (PM 1256/1259 -> 10085/10086)
* SM 600 `FW_reshape [5477] -> [5478]`                             (PM 1262/1263 -> 10139/10140)
* SM 601 `FW_mix_precision_linear [5478,5479] -> [5480]`           (PM 1264/1265 -> 10145/10146)
* SM 602 `FW_view [5480] -> [5481]`                                (PM 1266/1267 -> 10155/10156)
* SM 603 `FW_mul [5468,5481] -> [5482]` (broadcast `[N,1]x[N,1024]`)(PM 1268/1269 -> 10159/10160)
* SM 604 `FW_add [5463,5482] -> [5483]`                            (PM 1270/1271 -> 10163/10164)
* SM 605 `FW_float [5483] -> [5484]`                               (PM 1272/1273 -> 10169/10170)
* SM 606 `FW_add [8229,5484] -> [5485]`                            (PM 1274/1275 -> 10173/10174)
* SM 607 `FW_multiref [5485] -> [8256,8260]`                       (PM 1276/1277)
* SM 608 `FW_rms_norm [8256,5486] -> [5487]`                       (PM 1278/1279 -> 10177/10178)
* SM 609 `FW_per_head_mix_precision_linear [5487,5488] -> [5489]`  (PM 1280/1281 -> 10179/10180)

Two of the exported relations are **cross-layer boundary contracts**:

* `recon_zigzagGoal_8260_faithful` -- the cross-layer residual bypass consumed by
  block 3 (SM node 616 `FW_add`);
* `recon_zigzagGoal_5489_faithful` -- the per-head Q projection `[4096,16,64]` /
  `[2048,16,64]` feeding block 3's zigzag attention entry.

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

private theorem l14bt_reduce7
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

private theorem l14bt_reduce5
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
private def l14btSmMoE5463 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8240,5458,5459,5461,5462], outs := [5463],
    params := [64,0,64,8] }
private def l14btSmResh5478 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5477], outs := [5478],
    params := [4096,512] }
private def l14btSmMPL5480 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5478,5479], outs := [5480] }
private def l14btSmView5481 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5480], outs := [5481],
    params := [4096,1024] }
private def l14btSmMul5482 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5468,5481], outs := [5482] }
private def l14btSmAdd5483 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5463,5482], outs := [5483] }
private def l14btSmFloat5484 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5483], outs := [5484] }
private def l14btSmAdd5485 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8229,5484], outs := [5485] }
private def l14btSmMref5485 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5485], outs := [8256,8260],
    params := [2] }
private def l14btSmRms5487 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8256,5486], outs := [5487] }
private def l14btSmPhl5489 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5487,5488], outs := [5489] }

private def l14btPmMoE10085 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16164,10075,10077,10081,10083], outs := [10085],
    params := [64,0,32,8] }
private def l14btPmMoE10086 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16187,10076,10078,10082,10084], outs := [10086],
    params := [64,32,64,8] }
private def l14btPmResh10139 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10137], outs := [10139],
    params := [2048,512] }
private def l14btPmResh10140 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10138], outs := [10140],
    params := [2048,512] }
private def l14btPmMPL10145 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10139,5479], outs := [10145] }
private def l14btPmMPL10146 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10140,5479], outs := [10146] }
private def l14btPmView10155 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10145], outs := [10155],
    params := [2048,1024] }
private def l14btPmView10156 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10146], outs := [10156],
    params := [2048,1024] }
private def l14btPmMul10159 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [10099,10155], outs := [10159] }
private def l14btPmMul10160 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [10100,10156], outs := [10160] }
private def l14btPmAdd10163 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [10085,10159], outs := [10163] }
private def l14btPmAdd10164 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [10086,10160], outs := [10164] }
private def l14btPmFloat10169 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10163], outs := [10169] }
private def l14btPmFloat10170 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10164], outs := [10170] }
private def l14btPmAdd10173 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16145,10169], outs := [10173] }
private def l14btPmAdd10174 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16153,10170], outs := [10174] }
private def l14btPmMref10173 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10173], outs := [16203,16207],
    params := [2] }
private def l14btPmMref10174 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10174], outs := [16211,16215],
    params := [2] }
private def l14btPmRms10177 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16203,5486], outs := [10177] }
private def l14btPmRms10178 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16211,5486], outs := [10178] }
private def l14btPmPhl10179 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10177,5488], outs := [10179] }
private def l14btPmPhl10180 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10178,5488], outs := [10180] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l14bt_sm_node_facts :
    sm.nodes[597]'(by native_decide) = l14btSmMoE5463 ∧
    sm.nodes[600]'(by native_decide) = l14btSmResh5478 ∧
    sm.nodes[601]'(by native_decide) = l14btSmMPL5480 ∧
    sm.nodes[602]'(by native_decide) = l14btSmView5481 ∧
    sm.nodes[603]'(by native_decide) = l14btSmMul5482 ∧
    sm.nodes[604]'(by native_decide) = l14btSmAdd5483 ∧
    sm.nodes[605]'(by native_decide) = l14btSmFloat5484 ∧
    sm.nodes[606]'(by native_decide) = l14btSmAdd5485 ∧
    sm.nodes[607]'(by native_decide) = l14btSmMref5485 ∧
    sm.nodes[608]'(by native_decide) = l14btSmRms5487 ∧
    sm.nodes[609]'(by native_decide) = l14btSmPhl5489 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l14bt_pm_node_facts :
    pm.nodes[1256]'(by native_decide) = l14btPmMoE10085 ∧
    pm.nodes[1259]'(by native_decide) = l14btPmMoE10086 ∧
    pm.nodes[1262]'(by native_decide) = l14btPmResh10139 ∧
    pm.nodes[1263]'(by native_decide) = l14btPmResh10140 ∧
    pm.nodes[1264]'(by native_decide) = l14btPmMPL10145 ∧
    pm.nodes[1265]'(by native_decide) = l14btPmMPL10146 ∧
    pm.nodes[1266]'(by native_decide) = l14btPmView10155 ∧
    pm.nodes[1267]'(by native_decide) = l14btPmView10156 ∧
    pm.nodes[1268]'(by native_decide) = l14btPmMul10159 ∧
    pm.nodes[1269]'(by native_decide) = l14btPmMul10160 ∧
    pm.nodes[1270]'(by native_decide) = l14btPmAdd10163 ∧
    pm.nodes[1271]'(by native_decide) = l14btPmAdd10164 ∧
    pm.nodes[1272]'(by native_decide) = l14btPmFloat10169 ∧
    pm.nodes[1273]'(by native_decide) = l14btPmFloat10170 ∧
    pm.nodes[1274]'(by native_decide) = l14btPmAdd10173 ∧
    pm.nodes[1275]'(by native_decide) = l14btPmAdd10174 ∧
    pm.nodes[1276]'(by native_decide) = l14btPmMref10173 ∧
    pm.nodes[1277]'(by native_decide) = l14btPmMref10174 ∧
    pm.nodes[1278]'(by native_decide) = l14btPmRms10177 ∧
    pm.nodes[1279]'(by native_decide) = l14btPmRms10178 ∧
    pm.nodes[1280]'(by native_decide) = l14btPmPhl10179 ∧
    pm.nodes[1281]'(by native_decide) = l14btPmPhl10180 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l14bt_buddy_facts :
    sm.replicaBuddies l14btSmMoE5463 = [l14btSmMoE5463] ∧
    pm.replicaBuddies l14btPmMoE10085 = [l14btPmMoE10085, l14btPmMoE10086] ∧
    pm.replicaBuddies l14btPmMoE10086 = [l14btPmMoE10085, l14btPmMoE10086] := by
  native_decide

private theorem l14bt_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l14bt_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l14bt_weights_not_written :
    ((∀ n ∈ sm.nodes, 5479 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5486 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5488 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5479 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5486 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5488 ∉ n.outs)) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l14bt_cu_not_written : ∀ n ∈ pm.nodes, 5443 ∉ n.outs := by
  native_decide

private theorem l14bt_w5479_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5479 ∉ n.outs := by
  intro n hn
  exact l14bt_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l14bt_w5479_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5479 ∉ n.outs := by
  intro n hn
  exact l14bt_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l14bt_w5486_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5486 ∉ n.outs := by
  intro n hn
  exact l14bt_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l14bt_w5486_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5486 ∉ n.outs := by
  intro n hn
  exact l14bt_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l14bt_w5488_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5488 ∉ n.outs := by
  intro n hn
  exact l14bt_weights_not_written.1.2.2 n (List.mem_of_mem_drop hn)

private theorem l14bt_w5488_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5488 ∉ n.outs := by
  intro n hn
  exact l14bt_weights_not_written.2.2.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l14bt_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(598, 5463), (597, 8240), (597, 5458), (597, 5459), (597, 5461), (597, 5462), (601, 5478), (600, 5477), (602, 5480), (601, 5478), (603, 5481), (602, 5480), (604, 5482), (603, 5468), (603, 5481), (605, 5483), (604, 5463), (604, 5482), (606, 5484), (605, 5483), (607, 5485), (606, 8229), (606, 5484), (608, 8256), (608, 8260), (607, 5485), (609, 5487), (608, 8256), (610, 5489), (609, 5487)]) :
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
private theorem l14bt_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1257, 10085), (1256, 16164), (1256, 10075), (1256, 10077), (1256, 10081), (1256, 10083), (1256, 10082), (1256, 10084), (1260, 10086), (1259, 16187), (1259, 10076), (1259, 10078), (1259, 10081), (1259, 10082), (1259, 10083), (1259, 10084), (1263, 10139), (1262, 10137), (1264, 10140), (1263, 10138), (1265, 10145), (1264, 10139), (1266, 10146), (1265, 10140), (1267, 10155), (1266, 10145), (1268, 10156), (1267, 10146), (1269, 10159), (1268, 10099), (1268, 10155), (1270, 10160), (1269, 10100), (1269, 10156), (1271, 10163), (1270, 10085), (1270, 10159), (1272, 10164), (1271, 10086), (1271, 10160), (1273, 10169), (1272, 10163), (1274, 10170), (1273, 10164), (1275, 10173), (1274, 16145), (1274, 10169), (1276, 10174), (1275, 16153), (1275, 10170), (1277, 16203), (1277, 16207), (1276, 10173), (1278, 16211), (1278, 16215), (1277, 10174), (1279, 10177), (1278, 16203), (1280, 10178), (1279, 16211), (1281, 10179), (1280, 10177), (1282, 10180), (1281, 10178)]) :
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
private theorem l14bt_sm_leaf_not_written (tid : Nat)
    (h : tid ∈ [5461, 5462]) : ∀ n ∈ sm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l14bt_pm_leaf_not_written (tid : Nat)
    (h : tid ∈ [10081, 10082, 10083, 10084]) : ∀ n ∈ pm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> native_decide +revert

private theorem l14bt_sm_leaf (initSM : Store) (tid : Nat) (h : tid ∈ [5461, 5462]) :
    denoteGraphDistributedFaithful sm initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
    layer1_sm_nodes_nonempty (l14bt_sm_leaf_not_written tid h)

private theorem l14bt_pm_leaf (initPM : Store) (tid : Nat)
    (h : tid ∈ [10081, 10082, 10083, 10084]) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty (l14bt_pm_leaf_not_written tid h)

private theorem l14bt_pmFinal (initPM : Store) (tid : Tid)
    (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty hw

/-! ### Node reductions: MoE expert 5463 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_sm5463 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5463 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm initSM 8240)
        (denoteGraphDistributedFaithful sm initSM 5458)
        (denoteGraphDistributedFaithful sm initSM 5459)
        [denoteGraphDistributedFaithful sm initSM 5461]
        [denoteGraphDistributedFaithful sm initSM 5462]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l14bt_reduce5 sm initSM 597 l14btSmMoE5463
    8240 5458 5459 5461 5462 5463
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2] 64 8
      (((10 : Nat) : Scalar)))
    (by native_decide) l14bt_sm_node_facts.1 ?_
    (l14bt_nonempty_sm 598) (l14bt_sm_not_written 598 5463 (by decide))
    (l14bt_nonempty_sm 597) (l14bt_sm_not_written 597 8240 (by decide))
    (l14bt_sm_not_written 597 5458 (by decide))
    (l14bt_sm_not_written 597 5459 (by decide))
    (l14bt_sm_not_written 597 5461 (by decide))
    (l14bt_sm_not_written 597 5462 (by decide))
  intro s
  have hb := l14bt_buddy_facts.1
  unfold l14btSmMoE5463 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm s 0 8240 5458 5459 5461 5462 5463 [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10085 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10085 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16164)
        (denoteGraphDistributedFaithful pm initPM 10075)
        (denoteGraphDistributedFaithful pm initPM 10077)
        [denoteGraphDistributedFaithful pm initPM 10081,
         denoteGraphDistributedFaithful pm initPM 10082]
        [denoteGraphDistributedFaithful pm initPM 10083,
         denoteGraphDistributedFaithful pm initPM 10084]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l14bt_reduce7 pm initPM 1256 l14btPmMoE10085
    16164 10075 10077 10081 10083 10082 10084 10085
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l14bt_pm_node_facts.1 ?_
    (l14bt_nonempty_pm 1257) (l14bt_pm_not_written 1257 10085 (by decide))
    (l14bt_nonempty_pm 1256) (l14bt_pm_not_written 1256 16164 (by decide))
    (l14bt_pm_not_written 1256 10075 (by decide))
    (l14bt_pm_not_written 1256 10077 (by decide))
    (l14bt_pm_not_written 1256 10081 (by decide))
    (l14bt_pm_not_written 1256 10083 (by decide))
    (l14bt_pm_not_written 1256 10082 (by decide))
    (l14bt_pm_not_written 1256 10084 (by decide))
  intro s
  have hb := l14bt_buddy_facts.2.1
  unfold l14btPmMoE10085 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 0 16164 10075 10077 10081 10083 10085 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10086 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10086 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16187)
        (denoteGraphDistributedFaithful pm initPM 10076)
        (denoteGraphDistributedFaithful pm initPM 10078)
        [denoteGraphDistributedFaithful pm initPM 10081,
         denoteGraphDistributedFaithful pm initPM 10082]
        [denoteGraphDistributedFaithful pm initPM 10083,
         denoteGraphDistributedFaithful pm initPM 10084]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l14bt_reduce7 pm initPM 1259 l14btPmMoE10086
    16187 10076 10078 10081 10082 10083 10084 10086
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l14bt_pm_node_facts.2.1 ?_
    (l14bt_nonempty_pm 1260) (l14bt_pm_not_written 1260 10086 (by decide))
    (l14bt_nonempty_pm 1259) (l14bt_pm_not_written 1259 16187 (by decide))
    (l14bt_pm_not_written 1259 10076 (by decide))
    (l14bt_pm_not_written 1259 10078 (by decide))
    (l14bt_pm_not_written 1259 10081 (by decide))
    (l14bt_pm_not_written 1259 10082 (by decide))
    (l14bt_pm_not_written 1259 10083 (by decide))
    (l14bt_pm_not_written 1259 10084 (by decide))
  intro s
  have hb := l14bt_buddy_facts.2.2
  unfold l14btPmMoE10086 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 1 16187 10076 10078 10082 10084 10086 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

/-! ### Node reductions: reshape 5478 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_sm5478 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5478 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5477) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 600 l14btSmResh5478
    5477 5478 (fun x => fw_view [4096,512] x)
    (by native_decide) l14bt_sm_node_facts.2.1 ?_
    (l14bt_nonempty_sm 601) (l14bt_sm_not_written 601 5478 (by decide))
    (l14bt_nonempty_sm 600) (l14bt_sm_not_written 600 5477 (by decide))
  intro s
  unfold l14btSmResh5478
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5477 5478 [4096,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10139 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10139 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10137) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1262 l14btPmResh10139
    10137 10139 (fun x => fw_view [2048,512] x)
    (by native_decide) l14bt_pm_node_facts.2.2.1 ?_
    (l14bt_nonempty_pm 1263) (l14bt_pm_not_written 1263 10139 (by decide))
    (l14bt_nonempty_pm 1262) (l14bt_pm_not_written 1262 10137 (by decide))
  intro s
  unfold l14btPmResh10139
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10137 10139 [2048,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10140 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10140 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10138) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1263 l14btPmResh10140
    10138 10140 (fun x => fw_view [2048,512] x)
    (by native_decide) l14bt_pm_node_facts.2.2.2.1 ?_
    (l14bt_nonempty_pm 1264) (l14bt_pm_not_written 1264 10140 (by decide))
    (l14bt_nonempty_pm 1263) (l14bt_pm_not_written 1263 10138 (by decide))
  intro s
  unfold l14btPmResh10140
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10138 10140 [2048,512]

/-! ### Node reductions: down-projection 5480 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_sm5480 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5480 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5478)
        (denoteGraphDistributedFaithful sm initSM 5479) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 601 l14btSmMPL5480
    5478 5479 5480 fw_linear
    (by native_decide) l14bt_sm_node_facts.2.2.1 ?_
    (l14bt_nonempty_sm 602) (l14bt_sm_not_written 602 5480 (by decide))
    (l14bt_nonempty_sm 601) (l14bt_sm_not_written 601 5478 (by decide))
    (l14bt_w5479_sm_drop 601)
  intro s
  unfold l14btSmMPL5480
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5478 5479 5480

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10145 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10145 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10139)
        (denoteGraphDistributedFaithful pm initPM 5479) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1264 l14btPmMPL10145
    10139 5479 10145 fw_linear
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1265) (l14bt_pm_not_written 1265 10145 (by decide))
    (l14bt_nonempty_pm 1264) (l14bt_pm_not_written 1264 10139 (by decide))
    (l14bt_w5479_pm_drop 1264)
  intro s
  unfold l14btPmMPL10145
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10139 5479 10145

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10146 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10146 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10140)
        (denoteGraphDistributedFaithful pm initPM 5479) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1265 l14btPmMPL10146
    10140 5479 10146 fw_linear
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1266) (l14bt_pm_not_written 1266 10146 (by decide))
    (l14bt_nonempty_pm 1265) (l14bt_pm_not_written 1265 10140 (by decide))
    (l14bt_w5479_pm_drop 1265)
  intro s
  unfold l14btPmMPL10146
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10140 5479 10146

/-! ### Node reductions: view 5481 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_sm5481 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5481 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 5480) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 602 l14btSmView5481
    5480 5481 (fun x => fw_view [4096,1024] x)
    (by native_decide) l14bt_sm_node_facts.2.2.2.1 ?_
    (l14bt_nonempty_sm 603) (l14bt_sm_not_written 603 5481 (by decide))
    (l14bt_nonempty_sm 602) (l14bt_sm_not_written 602 5480 (by decide))
  intro s
  unfold l14btSmView5481
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5480 5481

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10155 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10155 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 10145) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1266 l14btPmView10155
    10145 10155 (fun x => fw_view [2048,1024] x)
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1267) (l14bt_pm_not_written 1267 10155 (by decide))
    (l14bt_nonempty_pm 1266) (l14bt_pm_not_written 1266 10145 (by decide))
  intro s
  unfold l14btPmView10155
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 10145 10155

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10156 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10156 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 10146) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1267 l14btPmView10156
    10146 10156 (fun x => fw_view [2048,1024] x)
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1268) (l14bt_pm_not_written 1268 10156 (by decide))
    (l14bt_nonempty_pm 1267) (l14bt_pm_not_written 1267 10146 (by decide))
  intro s
  unfold l14btPmView10156
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 10146 10156

/-! ### Node reductions: gated multiply 5482 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_sm5482 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5482 =
      elemwiseMul (denoteGraphDistributedFaithful sm initSM 5468)
        (denoteGraphDistributedFaithful sm initSM 5481) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 603 l14btSmMul5482
    5468 5481 5482 elemwiseMul
    (by native_decide) l14bt_sm_node_facts.2.2.2.2.1 ?_
    (l14bt_nonempty_sm 604) (l14bt_sm_not_written 604 5482 (by decide))
    (l14bt_nonempty_sm 603) (l14bt_sm_not_written 603 5468 (by decide))
    (l14bt_sm_not_written 603 5481 (by decide))
  intro s
  unfold l14btSmMul5482
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm s 0 5468 5481 5482

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10159 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10159 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 10099)
        (denoteGraphDistributedFaithful pm initPM 10155) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1268 l14btPmMul10159
    10099 10155 10159 elemwiseMul
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1269) (l14bt_pm_not_written 1269 10159 (by decide))
    (l14bt_nonempty_pm 1268) (l14bt_pm_not_written 1268 10099 (by decide))
    (l14bt_pm_not_written 1268 10155 (by decide))
  intro s
  unfold l14btPmMul10159
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 0 10099 10155 10159

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10160 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10160 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 10100)
        (denoteGraphDistributedFaithful pm initPM 10156) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1269 l14btPmMul10160
    10100 10156 10160 elemwiseMul
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1270) (l14bt_pm_not_written 1270 10160 (by decide))
    (l14bt_nonempty_pm 1269) (l14bt_pm_not_written 1269 10100 (by decide))
    (l14bt_pm_not_written 1269 10156 (by decide))
  intro s
  unfold l14btPmMul10160
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 1 10100 10156 10160

/-! ### Node reductions: MoE join 5483 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_sm5483 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5483 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 5463)
        (denoteGraphDistributedFaithful sm initSM 5482) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 604 l14btSmAdd5483
    5463 5482 5483 elemwiseAdd
    (by native_decide) l14bt_sm_node_facts.2.2.2.2.2.1 ?_
    (l14bt_nonempty_sm 605) (l14bt_sm_not_written 605 5483 (by decide))
    (l14bt_nonempty_sm 604) (l14bt_sm_not_written 604 5463 (by decide))
    (l14bt_sm_not_written 604 5482 (by decide))
  intro s
  unfold l14btSmAdd5483
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 5463 5482 5483

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10163 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10163 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 10085)
        (denoteGraphDistributedFaithful pm initPM 10159) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1270 l14btPmAdd10163
    10085 10159 10163 elemwiseAdd
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1271) (l14bt_pm_not_written 1271 10163 (by decide))
    (l14bt_nonempty_pm 1270) (l14bt_pm_not_written 1270 10085 (by decide))
    (l14bt_pm_not_written 1270 10159 (by decide))
  intro s
  unfold l14btPmAdd10163
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 10085 10159 10163

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10164 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10164 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 10086)
        (denoteGraphDistributedFaithful pm initPM 10160) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1271 l14btPmAdd10164
    10086 10160 10164 elemwiseAdd
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1272) (l14bt_pm_not_written 1272 10164 (by decide))
    (l14bt_nonempty_pm 1271) (l14bt_pm_not_written 1271 10086 (by decide))
    (l14bt_pm_not_written 1271 10160 (by decide))
  intro s
  unfold l14btPmAdd10164
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 10086 10160 10164

/-! ### Node reductions: float 5484 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_sm5484 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5484 =
      denoteGraphDistributedFaithful sm initSM 5483 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 605 l14btSmFloat5484
    5483 5484 (fun x => x)
    (by native_decide) l14bt_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_sm 606) (l14bt_sm_not_written 606 5484 (by decide))
    (l14bt_nonempty_sm 605) (l14bt_sm_not_written 605 5483 (by decide))
  intro s
  unfold l14btSmFloat5484
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 5483 5484 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10169 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10169 =
      denoteGraphDistributedFaithful pm initPM 10163 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1272 l14btPmFloat10169
    10163 10169 (fun x => x)
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1273) (l14bt_pm_not_written 1273 10169 (by decide))
    (l14bt_nonempty_pm 1272) (l14bt_pm_not_written 1272 10163 (by decide))
  intro s
  unfold l14btPmFloat10169
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 10163 10169 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10170 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10170 =
      denoteGraphDistributedFaithful pm initPM 10164 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1273 l14btPmFloat10170
    10164 10170 (fun x => x)
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1274) (l14bt_pm_not_written 1274 10170 (by decide))
    (l14bt_nonempty_pm 1273) (l14bt_pm_not_written 1273 10164 (by decide))
  intro s
  unfold l14btPmFloat10170
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 10164 10170 []

/-! ### Node reductions: residual join 5485 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_sm5485 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5485 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8229)
        (denoteGraphDistributedFaithful sm initSM 5484) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 606 l14btSmAdd5485
    8229 5484 5485 elemwiseAdd
    (by native_decide) l14bt_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_sm 607) (l14bt_sm_not_written 607 5485 (by decide))
    (l14bt_nonempty_sm 606) (l14bt_sm_not_written 606 8229 (by decide))
    (l14bt_sm_not_written 606 5484 (by decide))
  intro s
  unfold l14btSmAdd5485
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8229 5484 5485

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10173 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10173 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16145)
        (denoteGraphDistributedFaithful pm initPM 10169) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1274 l14btPmAdd10173
    16145 10169 10173 elemwiseAdd
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1275) (l14bt_pm_not_written 1275 10173 (by decide))
    (l14bt_nonempty_pm 1274) (l14bt_pm_not_written 1274 16145 (by decide))
    (l14bt_pm_not_written 1274 10169 (by decide))
  intro s
  unfold l14btPmAdd10173
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16145 10169 10173

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10174 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10174 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16153)
        (denoteGraphDistributedFaithful pm initPM 10170) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1275 l14btPmAdd10174
    16153 10170 10174 elemwiseAdd
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1276) (l14bt_pm_not_written 1276 10174 (by decide))
    (l14bt_nonempty_pm 1275) (l14bt_pm_not_written 1275 16153 (by decide))
    (l14bt_pm_not_written 1275 10170 (by decide))
  intro s
  unfold l14btPmAdd10174
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16153 10170 10174

/-! ### Node reductions: 2-way multiref off 5485 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_sm8256 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8256 =
      denoteGraphDistributedFaithful sm initSM 5485 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 607 l14btSmMref5485
    5485 8256 (fun x => x)
    (by native_decide) l14bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_sm 608) (l14bt_sm_not_written 608 8256 (by decide))
    (l14bt_nonempty_sm 607) (l14bt_sm_not_written 607 5485 (by decide))
  intro s
  unfold l14btSmMref5485
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5485 8256 8260

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_sm8260 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8260 =
      denoteGraphDistributedFaithful sm initSM 5485 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 607 l14btSmMref5485
    5485 8260 (fun x => x)
    (by native_decide) l14bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_sm 608) (l14bt_sm_not_written 608 8260 (by decide))
    (l14bt_nonempty_sm 607) (l14bt_sm_not_written 607 5485 (by decide))
  intro s
  unfold l14btSmMref5485
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5485 8256 8260 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm16203 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16203 =
      denoteGraphDistributedFaithful pm initPM 10173 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1276 l14btPmMref10173
    10173 16203 (fun x => x)
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1277) (l14bt_pm_not_written 1277 16203 (by decide))
    (l14bt_nonempty_pm 1276) (l14bt_pm_not_written 1276 10173 (by decide))
  intro s
  unfold l14btPmMref10173
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 10173 16203 16207

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm16207 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16207 =
      denoteGraphDistributedFaithful pm initPM 10173 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1276 l14btPmMref10173
    10173 16207 (fun x => x)
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1277) (l14bt_pm_not_written 1277 16207 (by decide))
    (l14bt_nonempty_pm 1276) (l14bt_pm_not_written 1276 10173 (by decide))
  intro s
  unfold l14btPmMref10173
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 10173 16203 16207 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm16211 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16211 =
      denoteGraphDistributedFaithful pm initPM 10174 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1277 l14btPmMref10174
    10174 16211 (fun x => x)
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1278) (l14bt_pm_not_written 1278 16211 (by decide))
    (l14bt_nonempty_pm 1277) (l14bt_pm_not_written 1277 10174 (by decide))
  intro s
  unfold l14btPmMref10174
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 10174 16211 16215

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm16215 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16215 =
      denoteGraphDistributedFaithful pm initPM 10174 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1277 l14btPmMref10174
    10174 16215 (fun x => x)
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1278) (l14bt_pm_not_written 1278 16215 (by decide))
    (l14bt_nonempty_pm 1277) (l14bt_pm_not_written 1277 10174 (by decide))
  intro s
  unfold l14btPmMref10174
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 10174 16211 16215 (by decide)

/-! ### Node reductions: RMSNorm 5487 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_sm5487 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5487 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8256)
        (denoteGraphDistributedFaithful sm initSM 5486) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 608 l14btSmRms5487
    8256 5486 5487 fw_rms_norm
    (by native_decide) l14bt_sm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_sm 609) (l14bt_sm_not_written 609 5487 (by decide))
    (l14bt_nonempty_sm 608) (l14bt_sm_not_written 608 8256 (by decide))
    (l14bt_w5486_sm_drop 608)
  intro s
  unfold l14btSmRms5487
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8256 5486 5487

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10177 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10177 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16203)
        (denoteGraphDistributedFaithful pm initPM 5486) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1278 l14btPmRms10177
    16203 5486 10177 fw_rms_norm
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1279) (l14bt_pm_not_written 1279 10177 (by decide))
    (l14bt_nonempty_pm 1278) (l14bt_pm_not_written 1278 16203 (by decide))
    (l14bt_w5486_pm_drop 1278)
  intro s
  unfold l14btPmRms10177
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16203 5486 10177

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10178 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10178 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16211)
        (denoteGraphDistributedFaithful pm initPM 5486) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1279 l14btPmRms10178
    16211 5486 10178 fw_rms_norm
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1280) (l14bt_pm_not_written 1280 10178 (by decide))
    (l14bt_nonempty_pm 1279) (l14bt_pm_not_written 1279 16211 (by decide))
    (l14bt_w5486_pm_drop 1279)
  intro s
  unfold l14btPmRms10178
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16211 5486 10178

/-! ### Node reductions: per-head Q projection 5489 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_sm5489 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5489 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 5487)
        (denoteGraphDistributedFaithful sm initSM 5488) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 609 l14btSmPhl5489
    5487 5488 5489 fw_per_head_linear
    (by native_decide) l14bt_sm_node_facts.2.2.2.2.2.2.2.2.2.2 ?_
    (l14bt_nonempty_sm 610) (l14bt_sm_not_written 610 5489 (by decide))
    (l14bt_nonempty_sm 609) (l14bt_sm_not_written 609 5487 (by decide))
    (l14bt_w5488_sm_drop 609)
  intro s
  unfold l14btSmPhl5489
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 5487 5488 5489 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10179 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10179 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 10177)
        (denoteGraphDistributedFaithful pm initPM 5488) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1280 l14btPmPhl10179
    10177 5488 10179 fw_per_head_linear
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14bt_nonempty_pm 1281) (l14bt_pm_not_written 1281 10179 (by decide))
    (l14bt_nonempty_pm 1280) (l14bt_pm_not_written 1280 10177 (by decide))
    (l14bt_w5488_pm_drop 1280)
  intro s
  unfold l14btPmPhl10179
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 0 10177 5488 10179 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_red_pm10180 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10180 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 10178)
        (denoteGraphDistributedFaithful pm initPM 5488) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1281 l14btPmPhl10180
    10178 5488 10180 fw_per_head_linear
    (by native_decide) l14bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l14bt_nonempty_pm 1282) (l14bt_pm_not_written 1282 10180 (by decide))
    (l14bt_nonempty_pm 1281) (l14bt_pm_not_written 1281 10178 (by decide))
    (l14bt_w5488_pm_drop 1281)
  intro s
  unfold l14btPmPhl10180
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 10178 5488 10180 []

/-! ### Shared helpers: weight transport and cu identification -/

set_option maxRecDepth 1000000 in
private theorem l14bt_weight_bridge (initSM initPM : Store)
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
private theorem l14bt_weight_eq (initSM initPM : Store)
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
private theorem l14bt_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  rw [l14bt_pmFinal initPM W hpw]
  exact hPM W sh hmem

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14bt_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5443) = [0, 2 * 2048] := by
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5443).shape = [2] := by
    rw [l14bt_pmFinal initPM 5443 l14bt_cu_not_written]
    exact hPM 5443 [2] (by native_decide)
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5443)).length = 2 := by
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
-- Faithful zigzag relation for generated goal 5463 (block-1 MoE expert layer).
theorem recon_zigzagGoal_5463_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5463)
      (denoteGraphDistributedFaithful pm initPM 10085)
      (denoteGraphDistributedFaithful pm initPM 10086)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hX := recon_zigzagGoal_8240_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRP := recon_zigzagGoal_5458_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRM := recon_zigzagGoal_5459_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l14bt_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8240)
      (denoteGraphDistributedFaithful pm initPM 16164)
      (denoteGraphDistributedFaithful pm initPM 16187)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5458)
      (denoteGraphDistributedFaithful pm initPM 10075)
      (denoteGraphDistributedFaithful pm initPM 10076)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5459)
      (denoteGraphDistributedFaithful pm initPM 10077)
      (denoteGraphDistributedFaithful pm initPM 10078)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 5461 = allGatherPrimDimN 0 2 0 [initPM 10081, initPM 10082] :=
    l14bt_weight_bridge initSM initPM hInit initGoal_5461 (by native_decide)
      5461 10081 10082 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5462 = allGatherPrimDimN 0 2 0 [initPM 10083, initPM 10084] :=
    l14bt_weight_bridge initSM initPM hInit initGoal_5462 (by native_decide)
      5462 10083 10084 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5461).shape = [64, 1024, 1024] :=
    hSM 5461 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5462).shape = [64, 1024, 512] :=
    hSM 5462 [64, 1024, 512] (by native_decide)
  rw [l14bt_red_sm5463 initSM, l14bt_red_pm10085 initPM, l14bt_red_pm10086 initPM]
  rw [l14bt_sm_leaf initSM 5461 (by decide), l14bt_sm_leaf initSM 5462 (by decide),
    l14bt_pm_leaf initPM 10081 (by decide), l14bt_pm_leaf initPM 10082 (by decide),
    l14bt_pm_leaf initPM 10083 (by decide), l14bt_pm_leaf initPM 10084 (by decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5461) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5462) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 10081, initPM 10082])
    (allGatherPrimDimN 0 2 0 [initPM 10083, initPM 10084])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5478 (`FW_reshape`).
theorem recon_zigzagGoal_5478_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5478)
      (denoteGraphDistributedFaithful pm initPM 10139)
      (denoteGraphDistributedFaithful pm initPM 10140)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 512] [2048, 512] := by
  have hparent := recon_zigzagGoal_5477_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14bt_red_sm5478 initSM, l14bt_red_pm10139 initPM, l14bt_red_pm10140 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5480 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5480_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5480)
      (denoteGraphDistributedFaithful pm initPM 10145)
      (denoteGraphDistributedFaithful pm initPM 10146)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5478_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5479 =
      denoteGraphDistributedFaithful pm initPM 5479 :=
    l14bt_weight_eq initSM initPM hInit 5479 initGoal_5479 (by native_decide)
      rfl rfl rfl rfl
      l14bt_weights_not_written.1.1 l14bt_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5479).shape = [1024, 512] :=
    l14bt_pm_weight_shape initPM hPM 5479 [1024, 512] (by native_decide)
      l14bt_weights_not_written.2.1
  rw [l14bt_red_sm5480 initSM, l14bt_red_pm10145 initPM, l14bt_red_pm10146 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5481 (`FW_view`).
theorem recon_zigzagGoal_5481_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5481)
      (denoteGraphDistributedFaithful pm initPM 10155)
      (denoteGraphDistributedFaithful pm initPM 10156)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5480_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14bt_red_sm5481 initSM, l14bt_red_pm10155 initPM, l14bt_red_pm10156 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5482 (broadcast `FW_mul`).
theorem recon_zigzagGoal_5482_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5482)
      (denoteGraphDistributedFaithful pm initPM 10159)
      (denoteGraphDistributedFaithful pm initPM 10160)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5468_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5481_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5468)
      (denoteGraphDistributedFaithful pm initPM 10099)
      (denoteGraphDistributedFaithful pm initPM 10100)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 1] [2048, 1] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5481)
      (denoteGraphDistributedFaithful pm initPM 10155)
      (denoteGraphDistributedFaithful pm initPM 10156)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l14bt_red_sm5482 initSM, l14bt_red_pm10159 initPM, l14bt_red_pm10160 initPM]
  exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5483 (`FW_add`, MoE join).
theorem recon_zigzagGoal_5483_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5483)
      (denoteGraphDistributedFaithful pm initPM 10163)
      (denoteGraphDistributedFaithful pm initPM 10164)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5463_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5482_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5463)
      (denoteGraphDistributedFaithful pm initPM 10085)
      (denoteGraphDistributedFaithful pm initPM 10086)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5482)
      (denoteGraphDistributedFaithful pm initPM 10159)
      (denoteGraphDistributedFaithful pm initPM 10160)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l14bt_red_sm5483 initSM, l14bt_red_pm10163 initPM, l14bt_red_pm10164 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5484 (`FW_float`, identity cast).
theorem recon_zigzagGoal_5484_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5484)
      (denoteGraphDistributedFaithful pm initPM 10169)
      (denoteGraphDistributedFaithful pm initPM 10170)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5483_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14bt_red_sm5484 initSM, l14bt_red_pm10169 initPM, l14bt_red_pm10170 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5485 (`FW_add`, residual join).
theorem recon_zigzagGoal_5485_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5485)
      (denoteGraphDistributedFaithful pm initPM 10173)
      (denoteGraphDistributedFaithful pm initPM 10174)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8229_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5484_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8229)
      (denoteGraphDistributedFaithful pm initPM 16145)
      (denoteGraphDistributedFaithful pm initPM 16153)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5484)
      (denoteGraphDistributedFaithful pm initPM 10169)
      (denoteGraphDistributedFaithful pm initPM 10170)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l14bt_red_sm5485 initSM, l14bt_red_pm10173 initPM, l14bt_red_pm10174 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8256 (multiref position 0 off 5485).
theorem recon_zigzagGoal_8256_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8256)
      (denoteGraphDistributedFaithful pm initPM 16203)
      (denoteGraphDistributedFaithful pm initPM 16211)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5485_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14bt_red_sm8256 initSM, l14bt_red_pm16203 initPM, l14bt_red_pm16211 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 8260 (multiref position 1
-- off 5485): the cross-layer residual bypass consumed by block 2's `FW_add`.
theorem recon_zigzagGoal_8260_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8260)
      (denoteGraphDistributedFaithful pm initPM 16207)
      (denoteGraphDistributedFaithful pm initPM 16215)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5485_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14bt_red_sm8260 initSM, l14bt_red_pm16207 initPM, l14bt_red_pm16215 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5487 (`FW_rms_norm`).
theorem recon_zigzagGoal_5487_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5487)
      (denoteGraphDistributedFaithful pm initPM 10177)
      (denoteGraphDistributedFaithful pm initPM 10178)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_8256_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5486 =
      denoteGraphDistributedFaithful pm initPM 5486 :=
    l14bt_weight_eq initSM initPM hInit 5486 initGoal_5486 (by native_decide)
      rfl rfl rfl rfl
      l14bt_weights_not_written.1.2.1 l14bt_weights_not_written.2.2.1
  rw [l14bt_red_sm5487 initSM, l14bt_red_pm10177 initPM, l14bt_red_pm10178 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 5489
-- (`FW_per_head_mix_precision_linear`): the per-head Q projection feeding block 2's
-- zigzag attention entry.
theorem recon_zigzagGoal_5489_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5489)
      (denoteGraphDistributedFaithful pm initPM 10179)
      (denoteGraphDistributedFaithful pm initPM 10180)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 16, 64] [2048, 16, 64] := by
  have hparent := recon_zigzagGoal_5487_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5488 =
      denoteGraphDistributedFaithful pm initPM 5488 :=
    l14bt_weight_eq initSM initPM hInit 5488 initGoal_5488 (by native_decide)
      rfl rfl rfl rfl
      l14bt_weights_not_written.1.2.2 l14bt_weights_not_written.2.2.2
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5488).shape = [16, 64, 1024] :=
    l14bt_pm_weight_shape initPM hPM 5488 [16, 64, 1024] (by native_decide)
      l14bt_weights_not_written.2.2.2
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5487)
      (denoteGraphDistributedFaithful pm initPM 10177)
      (denoteGraphDistributedFaithful pm initPM 10178)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l14bt_red_sm5489 initSM, l14bt_red_pm10179 initPM, l14bt_red_pm10180 initPM, hw]
  exact Zigzag2Rel.per_head_linear 2048 1024 16 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
