/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L15FaithfulMoEBranch
import denote.yoco_goals.L12FaithfulMoEExpert
import denote.yoco_goals.L12FaithfulMoEGate
import denote.yoco_goals.L14FaithfulBlockTail

/-!
# Faithful zigzag relations for the block-3 tail (MoE join -> block-3 Q)

Mechanical transport of the (green) block-2 tail `L13FaithfulBlockTail` to
block 3.  The block-3 cu tensor is **5492**.

* SM 632 `FW_all2all_moe_gmm [8279,5507,5508,5510,5511] -> [5512]` (PM 1326/1329 -> 10257/10258)
* SM 635 `FW_reshape [5526] -> [5527]`                             (PM 1332/1333 -> 10311/10312)
* SM 636 `FW_mix_precision_linear [5527,5528] -> [5529]`           (PM 1334/1335 -> 10317/10318)
* SM 637 `FW_view [5529] -> [5530]`                                (PM 1336/1337 -> 10327/10328)
* SM 638 `FW_mul [5517,5530] -> [5531]` (broadcast `[N,1]x[N,1024]`)(PM 1338/1339 -> 10331/10332)
* SM 639 `FW_add [5512,5531] -> [5532]`                            (PM 1340/1341 -> 10335/10336)
* SM 640 `FW_float [5532] -> [5533]`                               (PM 1342/1343 -> 10341/10342)
* SM 641 `FW_add [8268,5533] -> [5534]`                            (PM 1344/1345 -> 10345/10346)
* SM 642 `FW_multiref [5534] -> [8295,8299]`                       (PM 1346/1347)
* SM 643 `FW_rms_norm [8295,5535] -> [5536]`                       (PM 1348/1349 -> 10349/10350)
* SM 644 `FW_per_head_mix_precision_linear [5536,5537] -> [5538]`  (PM 1350/1351 -> 10351/10352)

Two of the exported relations are **cross-layer boundary contracts**:

* `recon_zigzagGoal_8299_faithful` -- the cross-layer residual bypass consumed by
  block 3 (SM node 651 `FW_add`);
* `recon_zigzagGoal_5538_faithful` -- the per-head Q projection `[4096,16,64]` /
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

private theorem l15bt_reduce7
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

private theorem l15bt_reduce5
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
private def l15btSmMoE5512 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8279,5507,5508,5510,5511], outs := [5512],
    params := [64,0,64,8] }
private def l15btSmResh5527 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5526], outs := [5527],
    params := [4096,512] }
private def l15btSmMPL5529 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5527,5528], outs := [5529] }
private def l15btSmView5530 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5529], outs := [5530],
    params := [4096,1024] }
private def l15btSmMul5531 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5517,5530], outs := [5531] }
private def l15btSmAdd5532 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5512,5531], outs := [5532] }
private def l15btSmFloat5533 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5532], outs := [5533] }
private def l15btSmAdd5534 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8268,5533], outs := [5534] }
private def l15btSmMref5534 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5534], outs := [8295,8299],
    params := [2] }
private def l15btSmRms5536 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8295,5535], outs := [5536] }
private def l15btSmPhl5538 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5536,5537], outs := [5538] }

private def l15btPmMoE10257 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16242,10247,10249,10253,10255], outs := [10257],
    params := [64,0,32,8] }
private def l15btPmMoE10258 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16265,10248,10250,10254,10256], outs := [10258],
    params := [64,32,64,8] }
private def l15btPmResh10311 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10309], outs := [10311],
    params := [2048,512] }
private def l15btPmResh10312 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10310], outs := [10312],
    params := [2048,512] }
private def l15btPmMPL10317 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10311,5528], outs := [10317] }
private def l15btPmMPL10318 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10312,5528], outs := [10318] }
private def l15btPmView10327 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10317], outs := [10327],
    params := [2048,1024] }
private def l15btPmView10328 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10318], outs := [10328],
    params := [2048,1024] }
private def l15btPmMul10331 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [10271,10327], outs := [10331] }
private def l15btPmMul10332 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [10272,10328], outs := [10332] }
private def l15btPmAdd10335 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [10257,10331], outs := [10335] }
private def l15btPmAdd10336 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [10258,10332], outs := [10336] }
private def l15btPmFloat10341 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10335], outs := [10341] }
private def l15btPmFloat10342 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10336], outs := [10342] }
private def l15btPmAdd10345 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16223,10341], outs := [10345] }
private def l15btPmAdd10346 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16231,10342], outs := [10346] }
private def l15btPmMref10345 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10345], outs := [16281,16285],
    params := [2] }
private def l15btPmMref10346 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10346], outs := [16289,16293],
    params := [2] }
private def l15btPmRms10349 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16281,5535], outs := [10349] }
private def l15btPmRms10350 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16289,5535], outs := [10350] }
private def l15btPmPhl10351 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10349,5537], outs := [10351] }
private def l15btPmPhl10352 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10350,5537], outs := [10352] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l15bt_sm_node_facts :
    sm.nodes[632]'(by native_decide) = l15btSmMoE5512 ∧
    sm.nodes[635]'(by native_decide) = l15btSmResh5527 ∧
    sm.nodes[636]'(by native_decide) = l15btSmMPL5529 ∧
    sm.nodes[637]'(by native_decide) = l15btSmView5530 ∧
    sm.nodes[638]'(by native_decide) = l15btSmMul5531 ∧
    sm.nodes[639]'(by native_decide) = l15btSmAdd5532 ∧
    sm.nodes[640]'(by native_decide) = l15btSmFloat5533 ∧
    sm.nodes[641]'(by native_decide) = l15btSmAdd5534 ∧
    sm.nodes[642]'(by native_decide) = l15btSmMref5534 ∧
    sm.nodes[643]'(by native_decide) = l15btSmRms5536 ∧
    sm.nodes[644]'(by native_decide) = l15btSmPhl5538 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l15bt_pm_node_facts :
    pm.nodes[1326]'(by native_decide) = l15btPmMoE10257 ∧
    pm.nodes[1329]'(by native_decide) = l15btPmMoE10258 ∧
    pm.nodes[1332]'(by native_decide) = l15btPmResh10311 ∧
    pm.nodes[1333]'(by native_decide) = l15btPmResh10312 ∧
    pm.nodes[1334]'(by native_decide) = l15btPmMPL10317 ∧
    pm.nodes[1335]'(by native_decide) = l15btPmMPL10318 ∧
    pm.nodes[1336]'(by native_decide) = l15btPmView10327 ∧
    pm.nodes[1337]'(by native_decide) = l15btPmView10328 ∧
    pm.nodes[1338]'(by native_decide) = l15btPmMul10331 ∧
    pm.nodes[1339]'(by native_decide) = l15btPmMul10332 ∧
    pm.nodes[1340]'(by native_decide) = l15btPmAdd10335 ∧
    pm.nodes[1341]'(by native_decide) = l15btPmAdd10336 ∧
    pm.nodes[1342]'(by native_decide) = l15btPmFloat10341 ∧
    pm.nodes[1343]'(by native_decide) = l15btPmFloat10342 ∧
    pm.nodes[1344]'(by native_decide) = l15btPmAdd10345 ∧
    pm.nodes[1345]'(by native_decide) = l15btPmAdd10346 ∧
    pm.nodes[1346]'(by native_decide) = l15btPmMref10345 ∧
    pm.nodes[1347]'(by native_decide) = l15btPmMref10346 ∧
    pm.nodes[1348]'(by native_decide) = l15btPmRms10349 ∧
    pm.nodes[1349]'(by native_decide) = l15btPmRms10350 ∧
    pm.nodes[1350]'(by native_decide) = l15btPmPhl10351 ∧
    pm.nodes[1351]'(by native_decide) = l15btPmPhl10352 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l15bt_buddy_facts :
    sm.replicaBuddies l15btSmMoE5512 = [l15btSmMoE5512] ∧
    pm.replicaBuddies l15btPmMoE10257 = [l15btPmMoE10257, l15btPmMoE10258] ∧
    pm.replicaBuddies l15btPmMoE10258 = [l15btPmMoE10257, l15btPmMoE10258] := by
  native_decide

private theorem l15bt_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l15bt_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l15bt_weights_not_written :
    ((∀ n ∈ sm.nodes, 5528 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5535 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5537 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5528 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5535 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5537 ∉ n.outs)) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l15bt_cu_not_written : ∀ n ∈ pm.nodes, 5492 ∉ n.outs := by
  native_decide

private theorem l15bt_w5528_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5528 ∉ n.outs := by
  intro n hn
  exact l15bt_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l15bt_w5528_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5528 ∉ n.outs := by
  intro n hn
  exact l15bt_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l15bt_w5535_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5535 ∉ n.outs := by
  intro n hn
  exact l15bt_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l15bt_w5535_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5535 ∉ n.outs := by
  intro n hn
  exact l15bt_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l15bt_w5537_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5537 ∉ n.outs := by
  intro n hn
  exact l15bt_weights_not_written.1.2.2 n (List.mem_of_mem_drop hn)

private theorem l15bt_w5537_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5537 ∉ n.outs := by
  intro n hn
  exact l15bt_weights_not_written.2.2.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l15bt_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(633, 5512), (632, 8279), (632, 5507), (632, 5508), (632, 5510), (632, 5511), (636, 5527), (635, 5526), (637, 5529), (636, 5527), (638, 5530), (637, 5529), (639, 5531), (638, 5517), (638, 5530), (640, 5532), (639, 5512), (639, 5531), (641, 5533), (640, 5532), (642, 5534), (641, 8268), (641, 5533), (643, 8295), (643, 8299), (642, 5534), (644, 5536), (643, 8295), (645, 5538), (644, 5536)]) :
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
private theorem l15bt_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1327, 10257), (1326, 16242), (1326, 10247), (1326, 10249), (1326, 10253), (1326, 10255), (1326, 10254), (1326, 10256), (1330, 10258), (1329, 16265), (1329, 10248), (1329, 10250), (1329, 10253), (1329, 10254), (1329, 10255), (1329, 10256), (1333, 10311), (1332, 10309), (1334, 10312), (1333, 10310), (1335, 10317), (1334, 10311), (1336, 10318), (1335, 10312), (1337, 10327), (1336, 10317), (1338, 10328), (1337, 10318), (1339, 10331), (1338, 10271), (1338, 10327), (1340, 10332), (1339, 10272), (1339, 10328), (1341, 10335), (1340, 10257), (1340, 10331), (1342, 10336), (1341, 10258), (1341, 10332), (1343, 10341), (1342, 10335), (1344, 10342), (1343, 10336), (1345, 10345), (1344, 16223), (1344, 10341), (1346, 10346), (1345, 16231), (1345, 10342), (1347, 16281), (1347, 16285), (1346, 10345), (1348, 16289), (1348, 16293), (1347, 10346), (1349, 10349), (1348, 16281), (1350, 10350), (1349, 16289), (1351, 10351), (1350, 10349), (1352, 10352), (1351, 10350)]) :
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
private theorem l15bt_sm_leaf_not_written (tid : Nat)
    (h : tid ∈ [5510, 5511]) : ∀ n ∈ sm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l15bt_pm_leaf_not_written (tid : Nat)
    (h : tid ∈ [10253, 10254, 10255, 10256]) : ∀ n ∈ pm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> native_decide +revert

private theorem l15bt_sm_leaf (initSM : Store) (tid : Nat) (h : tid ∈ [5510, 5511]) :
    denoteGraphDistributedFaithful sm initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
    layer1_sm_nodes_nonempty (l15bt_sm_leaf_not_written tid h)

private theorem l15bt_pm_leaf (initPM : Store) (tid : Nat)
    (h : tid ∈ [10253, 10254, 10255, 10256]) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty (l15bt_pm_leaf_not_written tid h)

private theorem l15bt_pmFinal (initPM : Store) (tid : Tid)
    (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty hw

/-! ### Node reductions: MoE expert 5512 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_sm5512 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5512 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm initSM 8279)
        (denoteGraphDistributedFaithful sm initSM 5507)
        (denoteGraphDistributedFaithful sm initSM 5508)
        [denoteGraphDistributedFaithful sm initSM 5510]
        [denoteGraphDistributedFaithful sm initSM 5511]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l15bt_reduce5 sm initSM 632 l15btSmMoE5512
    8279 5507 5508 5510 5511 5512
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2] 64 8
      (((10 : Nat) : Scalar)))
    (by native_decide) l15bt_sm_node_facts.1 ?_
    (l15bt_nonempty_sm 633) (l15bt_sm_not_written 633 5512 (by decide))
    (l15bt_nonempty_sm 632) (l15bt_sm_not_written 632 8279 (by decide))
    (l15bt_sm_not_written 632 5507 (by decide))
    (l15bt_sm_not_written 632 5508 (by decide))
    (l15bt_sm_not_written 632 5510 (by decide))
    (l15bt_sm_not_written 632 5511 (by decide))
  intro s
  have hb := l15bt_buddy_facts.1
  unfold l15btSmMoE5512 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm s 0 8279 5507 5508 5510 5511 5512 [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10257 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10257 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16242)
        (denoteGraphDistributedFaithful pm initPM 10247)
        (denoteGraphDistributedFaithful pm initPM 10249)
        [denoteGraphDistributedFaithful pm initPM 10253,
         denoteGraphDistributedFaithful pm initPM 10254]
        [denoteGraphDistributedFaithful pm initPM 10255,
         denoteGraphDistributedFaithful pm initPM 10256]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l15bt_reduce7 pm initPM 1326 l15btPmMoE10257
    16242 10247 10249 10253 10255 10254 10256 10257
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l15bt_pm_node_facts.1 ?_
    (l15bt_nonempty_pm 1327) (l15bt_pm_not_written 1327 10257 (by decide))
    (l15bt_nonempty_pm 1326) (l15bt_pm_not_written 1326 16242 (by decide))
    (l15bt_pm_not_written 1326 10247 (by decide))
    (l15bt_pm_not_written 1326 10249 (by decide))
    (l15bt_pm_not_written 1326 10253 (by decide))
    (l15bt_pm_not_written 1326 10255 (by decide))
    (l15bt_pm_not_written 1326 10254 (by decide))
    (l15bt_pm_not_written 1326 10256 (by decide))
  intro s
  have hb := l15bt_buddy_facts.2.1
  unfold l15btPmMoE10257 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 0 16242 10247 10249 10253 10255 10257 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10258 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10258 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16265)
        (denoteGraphDistributedFaithful pm initPM 10248)
        (denoteGraphDistributedFaithful pm initPM 10250)
        [denoteGraphDistributedFaithful pm initPM 10253,
         denoteGraphDistributedFaithful pm initPM 10254]
        [denoteGraphDistributedFaithful pm initPM 10255,
         denoteGraphDistributedFaithful pm initPM 10256]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l15bt_reduce7 pm initPM 1329 l15btPmMoE10258
    16265 10248 10250 10253 10254 10255 10256 10258
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l15bt_pm_node_facts.2.1 ?_
    (l15bt_nonempty_pm 1330) (l15bt_pm_not_written 1330 10258 (by decide))
    (l15bt_nonempty_pm 1329) (l15bt_pm_not_written 1329 16265 (by decide))
    (l15bt_pm_not_written 1329 10248 (by decide))
    (l15bt_pm_not_written 1329 10250 (by decide))
    (l15bt_pm_not_written 1329 10253 (by decide))
    (l15bt_pm_not_written 1329 10254 (by decide))
    (l15bt_pm_not_written 1329 10255 (by decide))
    (l15bt_pm_not_written 1329 10256 (by decide))
  intro s
  have hb := l15bt_buddy_facts.2.2
  unfold l15btPmMoE10258 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 1 16265 10248 10250 10254 10256 10258 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

/-! ### Node reductions: reshape 5527 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_sm5527 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5527 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5526) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 635 l15btSmResh5527
    5526 5527 (fun x => fw_view [4096,512] x)
    (by native_decide) l15bt_sm_node_facts.2.1 ?_
    (l15bt_nonempty_sm 636) (l15bt_sm_not_written 636 5527 (by decide))
    (l15bt_nonempty_sm 635) (l15bt_sm_not_written 635 5526 (by decide))
  intro s
  unfold l15btSmResh5527
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5526 5527 [4096,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10311 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10311 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10309) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1332 l15btPmResh10311
    10309 10311 (fun x => fw_view [2048,512] x)
    (by native_decide) l15bt_pm_node_facts.2.2.1 ?_
    (l15bt_nonempty_pm 1333) (l15bt_pm_not_written 1333 10311 (by decide))
    (l15bt_nonempty_pm 1332) (l15bt_pm_not_written 1332 10309 (by decide))
  intro s
  unfold l15btPmResh10311
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10309 10311 [2048,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10312 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10312 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10310) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1333 l15btPmResh10312
    10310 10312 (fun x => fw_view [2048,512] x)
    (by native_decide) l15bt_pm_node_facts.2.2.2.1 ?_
    (l15bt_nonempty_pm 1334) (l15bt_pm_not_written 1334 10312 (by decide))
    (l15bt_nonempty_pm 1333) (l15bt_pm_not_written 1333 10310 (by decide))
  intro s
  unfold l15btPmResh10312
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10310 10312 [2048,512]

/-! ### Node reductions: down-projection 5529 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_sm5529 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5529 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5527)
        (denoteGraphDistributedFaithful sm initSM 5528) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 636 l15btSmMPL5529
    5527 5528 5529 fw_linear
    (by native_decide) l15bt_sm_node_facts.2.2.1 ?_
    (l15bt_nonempty_sm 637) (l15bt_sm_not_written 637 5529 (by decide))
    (l15bt_nonempty_sm 636) (l15bt_sm_not_written 636 5527 (by decide))
    (l15bt_w5528_sm_drop 636)
  intro s
  unfold l15btSmMPL5529
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5527 5528 5529

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10317 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10317 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10311)
        (denoteGraphDistributedFaithful pm initPM 5528) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1334 l15btPmMPL10317
    10311 5528 10317 fw_linear
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1335) (l15bt_pm_not_written 1335 10317 (by decide))
    (l15bt_nonempty_pm 1334) (l15bt_pm_not_written 1334 10311 (by decide))
    (l15bt_w5528_pm_drop 1334)
  intro s
  unfold l15btPmMPL10317
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10311 5528 10317

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10318 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10318 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10312)
        (denoteGraphDistributedFaithful pm initPM 5528) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1335 l15btPmMPL10318
    10312 5528 10318 fw_linear
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1336) (l15bt_pm_not_written 1336 10318 (by decide))
    (l15bt_nonempty_pm 1335) (l15bt_pm_not_written 1335 10312 (by decide))
    (l15bt_w5528_pm_drop 1335)
  intro s
  unfold l15btPmMPL10318
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10312 5528 10318

/-! ### Node reductions: view 5530 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_sm5530 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5530 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 5529) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 637 l15btSmView5530
    5529 5530 (fun x => fw_view [4096,1024] x)
    (by native_decide) l15bt_sm_node_facts.2.2.2.1 ?_
    (l15bt_nonempty_sm 638) (l15bt_sm_not_written 638 5530 (by decide))
    (l15bt_nonempty_sm 637) (l15bt_sm_not_written 637 5529 (by decide))
  intro s
  unfold l15btSmView5530
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5529 5530

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10327 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10327 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 10317) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1336 l15btPmView10327
    10317 10327 (fun x => fw_view [2048,1024] x)
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1337) (l15bt_pm_not_written 1337 10327 (by decide))
    (l15bt_nonempty_pm 1336) (l15bt_pm_not_written 1336 10317 (by decide))
  intro s
  unfold l15btPmView10327
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 10317 10327

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10328 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10328 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 10318) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1337 l15btPmView10328
    10318 10328 (fun x => fw_view [2048,1024] x)
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1338) (l15bt_pm_not_written 1338 10328 (by decide))
    (l15bt_nonempty_pm 1337) (l15bt_pm_not_written 1337 10318 (by decide))
  intro s
  unfold l15btPmView10328
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 10318 10328

/-! ### Node reductions: gated multiply 5531 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_sm5531 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5531 =
      elemwiseMul (denoteGraphDistributedFaithful sm initSM 5517)
        (denoteGraphDistributedFaithful sm initSM 5530) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 638 l15btSmMul5531
    5517 5530 5531 elemwiseMul
    (by native_decide) l15bt_sm_node_facts.2.2.2.2.1 ?_
    (l15bt_nonempty_sm 639) (l15bt_sm_not_written 639 5531 (by decide))
    (l15bt_nonempty_sm 638) (l15bt_sm_not_written 638 5517 (by decide))
    (l15bt_sm_not_written 638 5530 (by decide))
  intro s
  unfold l15btSmMul5531
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm s 0 5517 5530 5531

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10331 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10331 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 10271)
        (denoteGraphDistributedFaithful pm initPM 10327) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1338 l15btPmMul10331
    10271 10327 10331 elemwiseMul
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1339) (l15bt_pm_not_written 1339 10331 (by decide))
    (l15bt_nonempty_pm 1338) (l15bt_pm_not_written 1338 10271 (by decide))
    (l15bt_pm_not_written 1338 10327 (by decide))
  intro s
  unfold l15btPmMul10331
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 0 10271 10327 10331

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10332 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10332 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 10272)
        (denoteGraphDistributedFaithful pm initPM 10328) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1339 l15btPmMul10332
    10272 10328 10332 elemwiseMul
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1340) (l15bt_pm_not_written 1340 10332 (by decide))
    (l15bt_nonempty_pm 1339) (l15bt_pm_not_written 1339 10272 (by decide))
    (l15bt_pm_not_written 1339 10328 (by decide))
  intro s
  unfold l15btPmMul10332
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 1 10272 10328 10332

/-! ### Node reductions: MoE join 5532 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_sm5532 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5532 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 5512)
        (denoteGraphDistributedFaithful sm initSM 5531) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 639 l15btSmAdd5532
    5512 5531 5532 elemwiseAdd
    (by native_decide) l15bt_sm_node_facts.2.2.2.2.2.1 ?_
    (l15bt_nonempty_sm 640) (l15bt_sm_not_written 640 5532 (by decide))
    (l15bt_nonempty_sm 639) (l15bt_sm_not_written 639 5512 (by decide))
    (l15bt_sm_not_written 639 5531 (by decide))
  intro s
  unfold l15btSmAdd5532
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 5512 5531 5532

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10335 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10335 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 10257)
        (denoteGraphDistributedFaithful pm initPM 10331) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1340 l15btPmAdd10335
    10257 10331 10335 elemwiseAdd
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1341) (l15bt_pm_not_written 1341 10335 (by decide))
    (l15bt_nonempty_pm 1340) (l15bt_pm_not_written 1340 10257 (by decide))
    (l15bt_pm_not_written 1340 10331 (by decide))
  intro s
  unfold l15btPmAdd10335
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 10257 10331 10335

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10336 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10336 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 10258)
        (denoteGraphDistributedFaithful pm initPM 10332) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1341 l15btPmAdd10336
    10258 10332 10336 elemwiseAdd
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1342) (l15bt_pm_not_written 1342 10336 (by decide))
    (l15bt_nonempty_pm 1341) (l15bt_pm_not_written 1341 10258 (by decide))
    (l15bt_pm_not_written 1341 10332 (by decide))
  intro s
  unfold l15btPmAdd10336
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 10258 10332 10336

/-! ### Node reductions: float 5533 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_sm5533 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5533 =
      denoteGraphDistributedFaithful sm initSM 5532 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 640 l15btSmFloat5533
    5532 5533 (fun x => x)
    (by native_decide) l15bt_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_sm 641) (l15bt_sm_not_written 641 5533 (by decide))
    (l15bt_nonempty_sm 640) (l15bt_sm_not_written 640 5532 (by decide))
  intro s
  unfold l15btSmFloat5533
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 5532 5533 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10341 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10341 =
      denoteGraphDistributedFaithful pm initPM 10335 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1342 l15btPmFloat10341
    10335 10341 (fun x => x)
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1343) (l15bt_pm_not_written 1343 10341 (by decide))
    (l15bt_nonempty_pm 1342) (l15bt_pm_not_written 1342 10335 (by decide))
  intro s
  unfold l15btPmFloat10341
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 10335 10341 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10342 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10342 =
      denoteGraphDistributedFaithful pm initPM 10336 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1343 l15btPmFloat10342
    10336 10342 (fun x => x)
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1344) (l15bt_pm_not_written 1344 10342 (by decide))
    (l15bt_nonempty_pm 1343) (l15bt_pm_not_written 1343 10336 (by decide))
  intro s
  unfold l15btPmFloat10342
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 10336 10342 []

/-! ### Node reductions: residual join 5534 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_sm5534 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5534 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8268)
        (denoteGraphDistributedFaithful sm initSM 5533) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 641 l15btSmAdd5534
    8268 5533 5534 elemwiseAdd
    (by native_decide) l15bt_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_sm 642) (l15bt_sm_not_written 642 5534 (by decide))
    (l15bt_nonempty_sm 641) (l15bt_sm_not_written 641 8268 (by decide))
    (l15bt_sm_not_written 641 5533 (by decide))
  intro s
  unfold l15btSmAdd5534
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8268 5533 5534

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10345 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10345 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16223)
        (denoteGraphDistributedFaithful pm initPM 10341) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1344 l15btPmAdd10345
    16223 10341 10345 elemwiseAdd
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1345) (l15bt_pm_not_written 1345 10345 (by decide))
    (l15bt_nonempty_pm 1344) (l15bt_pm_not_written 1344 16223 (by decide))
    (l15bt_pm_not_written 1344 10341 (by decide))
  intro s
  unfold l15btPmAdd10345
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16223 10341 10345

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10346 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10346 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16231)
        (denoteGraphDistributedFaithful pm initPM 10342) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1345 l15btPmAdd10346
    16231 10342 10346 elemwiseAdd
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1346) (l15bt_pm_not_written 1346 10346 (by decide))
    (l15bt_nonempty_pm 1345) (l15bt_pm_not_written 1345 16231 (by decide))
    (l15bt_pm_not_written 1345 10342 (by decide))
  intro s
  unfold l15btPmAdd10346
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16231 10342 10346

/-! ### Node reductions: 2-way multiref off 5534 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_sm8295 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8295 =
      denoteGraphDistributedFaithful sm initSM 5534 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 642 l15btSmMref5534
    5534 8295 (fun x => x)
    (by native_decide) l15bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_sm 643) (l15bt_sm_not_written 643 8295 (by decide))
    (l15bt_nonempty_sm 642) (l15bt_sm_not_written 642 5534 (by decide))
  intro s
  unfold l15btSmMref5534
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5534 8295 8299

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_sm8299 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8299 =
      denoteGraphDistributedFaithful sm initSM 5534 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 642 l15btSmMref5534
    5534 8299 (fun x => x)
    (by native_decide) l15bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_sm 643) (l15bt_sm_not_written 643 8299 (by decide))
    (l15bt_nonempty_sm 642) (l15bt_sm_not_written 642 5534 (by decide))
  intro s
  unfold l15btSmMref5534
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5534 8295 8299 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm16281 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16281 =
      denoteGraphDistributedFaithful pm initPM 10345 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1346 l15btPmMref10345
    10345 16281 (fun x => x)
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1347) (l15bt_pm_not_written 1347 16281 (by decide))
    (l15bt_nonempty_pm 1346) (l15bt_pm_not_written 1346 10345 (by decide))
  intro s
  unfold l15btPmMref10345
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 10345 16281 16285

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm16285 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16285 =
      denoteGraphDistributedFaithful pm initPM 10345 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1346 l15btPmMref10345
    10345 16285 (fun x => x)
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1347) (l15bt_pm_not_written 1347 16285 (by decide))
    (l15bt_nonempty_pm 1346) (l15bt_pm_not_written 1346 10345 (by decide))
  intro s
  unfold l15btPmMref10345
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 10345 16281 16285 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm16289 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16289 =
      denoteGraphDistributedFaithful pm initPM 10346 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1347 l15btPmMref10346
    10346 16289 (fun x => x)
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1348) (l15bt_pm_not_written 1348 16289 (by decide))
    (l15bt_nonempty_pm 1347) (l15bt_pm_not_written 1347 10346 (by decide))
  intro s
  unfold l15btPmMref10346
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 10346 16289 16293

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm16293 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16293 =
      denoteGraphDistributedFaithful pm initPM 10346 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1347 l15btPmMref10346
    10346 16293 (fun x => x)
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1348) (l15bt_pm_not_written 1348 16293 (by decide))
    (l15bt_nonempty_pm 1347) (l15bt_pm_not_written 1347 10346 (by decide))
  intro s
  unfold l15btPmMref10346
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 10346 16289 16293 (by decide)

/-! ### Node reductions: RMSNorm 5536 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_sm5536 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5536 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8295)
        (denoteGraphDistributedFaithful sm initSM 5535) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 643 l15btSmRms5536
    8295 5535 5536 fw_rms_norm
    (by native_decide) l15bt_sm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_sm 644) (l15bt_sm_not_written 644 5536 (by decide))
    (l15bt_nonempty_sm 643) (l15bt_sm_not_written 643 8295 (by decide))
    (l15bt_w5535_sm_drop 643)
  intro s
  unfold l15btSmRms5536
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8295 5535 5536

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10349 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10349 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16281)
        (denoteGraphDistributedFaithful pm initPM 5535) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1348 l15btPmRms10349
    16281 5535 10349 fw_rms_norm
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1349) (l15bt_pm_not_written 1349 10349 (by decide))
    (l15bt_nonempty_pm 1348) (l15bt_pm_not_written 1348 16281 (by decide))
    (l15bt_w5535_pm_drop 1348)
  intro s
  unfold l15btPmRms10349
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16281 5535 10349

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10350 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10350 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16289)
        (denoteGraphDistributedFaithful pm initPM 5535) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1349 l15btPmRms10350
    16289 5535 10350 fw_rms_norm
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1350) (l15bt_pm_not_written 1350 10350 (by decide))
    (l15bt_nonempty_pm 1349) (l15bt_pm_not_written 1349 16289 (by decide))
    (l15bt_w5535_pm_drop 1349)
  intro s
  unfold l15btPmRms10350
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16289 5535 10350

/-! ### Node reductions: per-head Q projection 5538 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_sm5538 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5538 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 5536)
        (denoteGraphDistributedFaithful sm initSM 5537) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 644 l15btSmPhl5538
    5536 5537 5538 fw_per_head_linear
    (by native_decide) l15bt_sm_node_facts.2.2.2.2.2.2.2.2.2.2 ?_
    (l15bt_nonempty_sm 645) (l15bt_sm_not_written 645 5538 (by decide))
    (l15bt_nonempty_sm 644) (l15bt_sm_not_written 644 5536 (by decide))
    (l15bt_w5537_sm_drop 644)
  intro s
  unfold l15btSmPhl5538
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 5536 5537 5538 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10351 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10351 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 10349)
        (denoteGraphDistributedFaithful pm initPM 5537) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1350 l15btPmPhl10351
    10349 5537 10351 fw_per_head_linear
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15bt_nonempty_pm 1351) (l15bt_pm_not_written 1351 10351 (by decide))
    (l15bt_nonempty_pm 1350) (l15bt_pm_not_written 1350 10349 (by decide))
    (l15bt_w5537_pm_drop 1350)
  intro s
  unfold l15btPmPhl10351
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 0 10349 5537 10351 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_red_pm10352 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10352 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 10350)
        (denoteGraphDistributedFaithful pm initPM 5537) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1351 l15btPmPhl10352
    10350 5537 10352 fw_per_head_linear
    (by native_decide) l15bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l15bt_nonempty_pm 1352) (l15bt_pm_not_written 1352 10352 (by decide))
    (l15bt_nonempty_pm 1351) (l15bt_pm_not_written 1351 10350 (by decide))
    (l15bt_w5537_pm_drop 1351)
  intro s
  unfold l15btPmPhl10352
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 10350 5537 10352 []

/-! ### Shared helpers: weight transport and cu identification -/

set_option maxRecDepth 1000000 in
private theorem l15bt_weight_bridge (initSM initPM : Store)
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
private theorem l15bt_weight_eq (initSM initPM : Store)
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
private theorem l15bt_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  rw [l15bt_pmFinal initPM W hpw]
  exact hPM W sh hmem

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15bt_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5492) = [0, 2 * 2048] := by
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5492).shape = [2] := by
    rw [l15bt_pmFinal initPM 5492 l15bt_cu_not_written]
    exact hPM 5492 [2] (by native_decide)
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5492)).length = 2 := by
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
-- Faithful zigzag relation for generated goal 5512 (block-2 MoE expert layer).
theorem recon_zigzagGoal_5512_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5512)
      (denoteGraphDistributedFaithful pm initPM 10257)
      (denoteGraphDistributedFaithful pm initPM 10258)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hX := recon_zigzagGoal_8279_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRP := recon_zigzagGoal_5507_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRM := recon_zigzagGoal_5508_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l15bt_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8279)
      (denoteGraphDistributedFaithful pm initPM 16242)
      (denoteGraphDistributedFaithful pm initPM 16265)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5507)
      (denoteGraphDistributedFaithful pm initPM 10247)
      (denoteGraphDistributedFaithful pm initPM 10248)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5508)
      (denoteGraphDistributedFaithful pm initPM 10249)
      (denoteGraphDistributedFaithful pm initPM 10250)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 5510 = allGatherPrimDimN 0 2 0 [initPM 10253, initPM 10254] :=
    l15bt_weight_bridge initSM initPM hInit initGoal_5510 (by native_decide)
      5510 10253 10254 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5511 = allGatherPrimDimN 0 2 0 [initPM 10255, initPM 10256] :=
    l15bt_weight_bridge initSM initPM hInit initGoal_5511 (by native_decide)
      5511 10255 10256 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5510).shape = [64, 1024, 1024] :=
    hSM 5510 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5511).shape = [64, 1024, 512] :=
    hSM 5511 [64, 1024, 512] (by native_decide)
  rw [l15bt_red_sm5512 initSM, l15bt_red_pm10257 initPM, l15bt_red_pm10258 initPM]
  rw [l15bt_sm_leaf initSM 5510 (by decide), l15bt_sm_leaf initSM 5511 (by decide),
    l15bt_pm_leaf initPM 10253 (by decide), l15bt_pm_leaf initPM 10254 (by decide),
    l15bt_pm_leaf initPM 10255 (by decide), l15bt_pm_leaf initPM 10256 (by decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5510) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5511) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 10253, initPM 10254])
    (allGatherPrimDimN 0 2 0 [initPM 10255, initPM 10256])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5527 (`FW_reshape`).
theorem recon_zigzagGoal_5527_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5527)
      (denoteGraphDistributedFaithful pm initPM 10311)
      (denoteGraphDistributedFaithful pm initPM 10312)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 512] [2048, 512] := by
  have hparent := recon_zigzagGoal_5526_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15bt_red_sm5527 initSM, l15bt_red_pm10311 initPM, l15bt_red_pm10312 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5529 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5529_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5529)
      (denoteGraphDistributedFaithful pm initPM 10317)
      (denoteGraphDistributedFaithful pm initPM 10318)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5527_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5528 =
      denoteGraphDistributedFaithful pm initPM 5528 :=
    l15bt_weight_eq initSM initPM hInit 5528 initGoal_5528 (by native_decide)
      rfl rfl rfl rfl
      l15bt_weights_not_written.1.1 l15bt_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5528).shape = [1024, 512] :=
    l15bt_pm_weight_shape initPM hPM 5528 [1024, 512] (by native_decide)
      l15bt_weights_not_written.2.1
  rw [l15bt_red_sm5529 initSM, l15bt_red_pm10317 initPM, l15bt_red_pm10318 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5530 (`FW_view`).
theorem recon_zigzagGoal_5530_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5530)
      (denoteGraphDistributedFaithful pm initPM 10327)
      (denoteGraphDistributedFaithful pm initPM 10328)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5529_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15bt_red_sm5530 initSM, l15bt_red_pm10327 initPM, l15bt_red_pm10328 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5531 (broadcast `FW_mul`).
theorem recon_zigzagGoal_5531_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5531)
      (denoteGraphDistributedFaithful pm initPM 10331)
      (denoteGraphDistributedFaithful pm initPM 10332)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5517_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5530_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5517)
      (denoteGraphDistributedFaithful pm initPM 10271)
      (denoteGraphDistributedFaithful pm initPM 10272)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 1] [2048, 1] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5530)
      (denoteGraphDistributedFaithful pm initPM 10327)
      (denoteGraphDistributedFaithful pm initPM 10328)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l15bt_red_sm5531 initSM, l15bt_red_pm10331 initPM, l15bt_red_pm10332 initPM]
  exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5532 (`FW_add`, MoE join).
theorem recon_zigzagGoal_5532_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5532)
      (denoteGraphDistributedFaithful pm initPM 10335)
      (denoteGraphDistributedFaithful pm initPM 10336)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5512_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5531_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5512)
      (denoteGraphDistributedFaithful pm initPM 10257)
      (denoteGraphDistributedFaithful pm initPM 10258)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5531)
      (denoteGraphDistributedFaithful pm initPM 10331)
      (denoteGraphDistributedFaithful pm initPM 10332)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l15bt_red_sm5532 initSM, l15bt_red_pm10335 initPM, l15bt_red_pm10336 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5533 (`FW_float`, identity cast).
theorem recon_zigzagGoal_5533_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5533)
      (denoteGraphDistributedFaithful pm initPM 10341)
      (denoteGraphDistributedFaithful pm initPM 10342)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5532_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15bt_red_sm5533 initSM, l15bt_red_pm10341 initPM, l15bt_red_pm10342 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5534 (`FW_add`, residual join).
theorem recon_zigzagGoal_5534_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5534)
      (denoteGraphDistributedFaithful pm initPM 10345)
      (denoteGraphDistributedFaithful pm initPM 10346)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8268_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5533_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8268)
      (denoteGraphDistributedFaithful pm initPM 16223)
      (denoteGraphDistributedFaithful pm initPM 16231)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5533)
      (denoteGraphDistributedFaithful pm initPM 10341)
      (denoteGraphDistributedFaithful pm initPM 10342)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l15bt_red_sm5534 initSM, l15bt_red_pm10345 initPM, l15bt_red_pm10346 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8295 (multiref position 0 off 5534).
theorem recon_zigzagGoal_8295_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8295)
      (denoteGraphDistributedFaithful pm initPM 16281)
      (denoteGraphDistributedFaithful pm initPM 16289)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5534_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15bt_red_sm8295 initSM, l15bt_red_pm16281 initPM, l15bt_red_pm16289 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 8299 (multiref position 1
-- off 5534): the cross-layer residual bypass consumed by block 3's `FW_add`.
theorem recon_zigzagGoal_8299_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8299)
      (denoteGraphDistributedFaithful pm initPM 16285)
      (denoteGraphDistributedFaithful pm initPM 16293)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5534_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15bt_red_sm8299 initSM, l15bt_red_pm16285 initPM, l15bt_red_pm16293 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5536 (`FW_rms_norm`).
theorem recon_zigzagGoal_5536_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5536)
      (denoteGraphDistributedFaithful pm initPM 10349)
      (denoteGraphDistributedFaithful pm initPM 10350)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_8295_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5535 =
      denoteGraphDistributedFaithful pm initPM 5535 :=
    l15bt_weight_eq initSM initPM hInit 5535 initGoal_5535 (by native_decide)
      rfl rfl rfl rfl
      l15bt_weights_not_written.1.2.1 l15bt_weights_not_written.2.2.1
  rw [l15bt_red_sm5536 initSM, l15bt_red_pm10349 initPM, l15bt_red_pm10350 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 5538
-- (`FW_per_head_mix_precision_linear`): the per-head Q projection feeding block 3's
-- zigzag attention entry.
theorem recon_zigzagGoal_5538_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5538)
      (denoteGraphDistributedFaithful pm initPM 10351)
      (denoteGraphDistributedFaithful pm initPM 10352)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 16, 64] [2048, 16, 64] := by
  have hparent := recon_zigzagGoal_5536_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5537 =
      denoteGraphDistributedFaithful pm initPM 5537 :=
    l15bt_weight_eq initSM initPM hInit 5537 initGoal_5537 (by native_decide)
      rfl rfl rfl rfl
      l15bt_weights_not_written.1.2.2 l15bt_weights_not_written.2.2.2
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5537).shape = [16, 64, 1024] :=
    l15bt_pm_weight_shape initPM hPM 5537 [16, 64, 1024] (by native_decide)
      l15bt_weights_not_written.2.2.2
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5536)
      (denoteGraphDistributedFaithful pm initPM 10349)
      (denoteGraphDistributedFaithful pm initPM 10350)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l15bt_red_sm5538 initSM, l15bt_red_pm10351 initPM, l15bt_red_pm10352 initPM, hw]
  exact Zigzag2Rel.per_head_linear 2048 1024 16 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
