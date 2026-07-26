/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L13FaithfulMoEBranch
import denote.yoco_goals.L12FaithfulMoEExpert
import denote.yoco_goals.L12FaithfulMoEGate
import denote.yoco_goals.L12FaithfulBlockTail

/-!
# Faithful zigzag relations for the block-1 tail (MoE join → block-2 Q)

* SM 562 `FW_all2all_moe_gmm [8201,5409,5410,5412,5413] → [5414]`  (PM 1186/1189 → 9913/9914)
* SM 565 `FW_reshape [5428] → [5429]`                              (PM 1192/1193 → 9967/9968)
* SM 566 `FW_mix_precision_linear [5429,5430] → [5431]`            (PM 1194/1195 → 9973/9974)
* SM 567 `FW_view [5431] → [5432]`                                 (PM 1196/1197 → 9983/9984)
* SM 568 `FW_mul [5419,5432] → [5433]` (broadcast `[N,1]x[N,1024]`)(PM 1198/1199 → 9987/9988)
* SM 569 `FW_add [5414,5433] → [5434]`                             (PM 1200/1201 → 9991/9992)
* SM 570 `FW_float [5434] → [5435]`                                (PM 1202/1203 → 9997/9998)
* SM 571 `FW_add [8190,5435] → [5436]`                             (PM 1204/1205 → 10001/10002)
* SM 572 `FW_multiref [5436] → [8217,8221]`                        (PM 1206/1207)
* SM 573 `FW_rms_norm [8217,5437] → [5438]`                        (PM 1208/1209 → 10005/10006)
* SM 574 `FW_per_head_mix_precision_linear [5438,5439] → [5440]`   (PM 1210/1211 → 10007/10008)

Two of the exported relations are **cross-layer boundary contracts**:

* `recon_zigzagGoal_8221_faithful` -- the cross-layer residual bypass consumed by
  block 2 (SM node 581 `FW_add`);
* `recon_zigzagGoal_5440_faithful` -- the per-head Q projection `[4096,16,64]` /
  `[2048,16,64]` feeding block 2's zigzag attention entry.

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

private theorem l13bt_reduce7
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

private theorem l13bt_reduce5
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
private def l13btSmMoE5414 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8201,5409,5410,5412,5413], outs := [5414],
    params := [64,0,64,8] }
private def l13btSmResh5429 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5428], outs := [5429],
    params := [4096,512] }
private def l13btSmMPL5431 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5429,5430], outs := [5431] }
private def l13btSmView5432 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5431], outs := [5432],
    params := [4096,1024] }
private def l13btSmMul5433 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5419,5432], outs := [5433] }
private def l13btSmAdd5434 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5414,5433], outs := [5434] }
private def l13btSmFloat5435 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5434], outs := [5435] }
private def l13btSmAdd5436 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8190,5435], outs := [5436] }
private def l13btSmMref5436 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5436], outs := [8217,8221],
    params := [2] }
private def l13btSmRms5438 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8217,5437], outs := [5438] }
private def l13btSmPhl5440 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5438,5439], outs := [5440] }

private def l13btPmMoE9913 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16086,9903,9905,9909,9911], outs := [9913],
    params := [64,0,32,8] }
private def l13btPmMoE9914 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16109,9904,9906,9910,9912], outs := [9914],
    params := [64,32,64,8] }
private def l13btPmResh9967 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9965], outs := [9967],
    params := [2048,512] }
private def l13btPmResh9968 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9966], outs := [9968],
    params := [2048,512] }
private def l13btPmMPL9973 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9967,5430], outs := [9973] }
private def l13btPmMPL9974 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9968,5430], outs := [9974] }
private def l13btPmView9983 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9973], outs := [9983],
    params := [2048,1024] }
private def l13btPmView9984 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9974], outs := [9984],
    params := [2048,1024] }
private def l13btPmMul9987 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [9927,9983], outs := [9987] }
private def l13btPmMul9988 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [9928,9984], outs := [9988] }
private def l13btPmAdd9991 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [9913,9987], outs := [9991] }
private def l13btPmAdd9992 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [9914,9988], outs := [9992] }
private def l13btPmFloat9997 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9991], outs := [9997] }
private def l13btPmFloat9998 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9992], outs := [9998] }
private def l13btPmAdd10001 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16067,9997], outs := [10001] }
private def l13btPmAdd10002 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16075,9998], outs := [10002] }
private def l13btPmMref10001 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10001], outs := [16125,16129],
    params := [2] }
private def l13btPmMref10002 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10002], outs := [16133,16137],
    params := [2] }
private def l13btPmRms10005 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16125,5437], outs := [10005] }
private def l13btPmRms10006 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16133,5437], outs := [10006] }
private def l13btPmPhl10007 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10005,5439], outs := [10007] }
private def l13btPmPhl10008 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10006,5439], outs := [10008] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l13bt_sm_node_facts :
    sm.nodes[562]'(by native_decide) = l13btSmMoE5414 ∧
    sm.nodes[565]'(by native_decide) = l13btSmResh5429 ∧
    sm.nodes[566]'(by native_decide) = l13btSmMPL5431 ∧
    sm.nodes[567]'(by native_decide) = l13btSmView5432 ∧
    sm.nodes[568]'(by native_decide) = l13btSmMul5433 ∧
    sm.nodes[569]'(by native_decide) = l13btSmAdd5434 ∧
    sm.nodes[570]'(by native_decide) = l13btSmFloat5435 ∧
    sm.nodes[571]'(by native_decide) = l13btSmAdd5436 ∧
    sm.nodes[572]'(by native_decide) = l13btSmMref5436 ∧
    sm.nodes[573]'(by native_decide) = l13btSmRms5438 ∧
    sm.nodes[574]'(by native_decide) = l13btSmPhl5440 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l13bt_pm_node_facts :
    pm.nodes[1186]'(by native_decide) = l13btPmMoE9913 ∧
    pm.nodes[1189]'(by native_decide) = l13btPmMoE9914 ∧
    pm.nodes[1192]'(by native_decide) = l13btPmResh9967 ∧
    pm.nodes[1193]'(by native_decide) = l13btPmResh9968 ∧
    pm.nodes[1194]'(by native_decide) = l13btPmMPL9973 ∧
    pm.nodes[1195]'(by native_decide) = l13btPmMPL9974 ∧
    pm.nodes[1196]'(by native_decide) = l13btPmView9983 ∧
    pm.nodes[1197]'(by native_decide) = l13btPmView9984 ∧
    pm.nodes[1198]'(by native_decide) = l13btPmMul9987 ∧
    pm.nodes[1199]'(by native_decide) = l13btPmMul9988 ∧
    pm.nodes[1200]'(by native_decide) = l13btPmAdd9991 ∧
    pm.nodes[1201]'(by native_decide) = l13btPmAdd9992 ∧
    pm.nodes[1202]'(by native_decide) = l13btPmFloat9997 ∧
    pm.nodes[1203]'(by native_decide) = l13btPmFloat9998 ∧
    pm.nodes[1204]'(by native_decide) = l13btPmAdd10001 ∧
    pm.nodes[1205]'(by native_decide) = l13btPmAdd10002 ∧
    pm.nodes[1206]'(by native_decide) = l13btPmMref10001 ∧
    pm.nodes[1207]'(by native_decide) = l13btPmMref10002 ∧
    pm.nodes[1208]'(by native_decide) = l13btPmRms10005 ∧
    pm.nodes[1209]'(by native_decide) = l13btPmRms10006 ∧
    pm.nodes[1210]'(by native_decide) = l13btPmPhl10007 ∧
    pm.nodes[1211]'(by native_decide) = l13btPmPhl10008 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l13bt_buddy_facts :
    sm.replicaBuddies l13btSmMoE5414 = [l13btSmMoE5414] ∧
    pm.replicaBuddies l13btPmMoE9913 = [l13btPmMoE9913, l13btPmMoE9914] ∧
    pm.replicaBuddies l13btPmMoE9914 = [l13btPmMoE9913, l13btPmMoE9914] := by
  native_decide

private theorem l13bt_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l13bt_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l13bt_weights_not_written :
    ((∀ n ∈ sm.nodes, 5430 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5437 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5439 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5430 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5437 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5439 ∉ n.outs)) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l13bt_cu_not_written :
    ∀ n ∈ pm.nodes, 5345 ∉ n.outs ∧ 5394 ∉ n.outs := by
  native_decide

private theorem l13bt_w5430_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5430 ∉ n.outs := by
  intro n hn
  exact l13bt_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l13bt_w5430_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5430 ∉ n.outs := by
  intro n hn
  exact l13bt_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l13bt_w5437_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5437 ∉ n.outs := by
  intro n hn
  exact l13bt_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l13bt_w5437_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5437 ∉ n.outs := by
  intro n hn
  exact l13bt_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l13bt_w5439_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5439 ∉ n.outs := by
  intro n hn
  exact l13bt_weights_not_written.1.2.2 n (List.mem_of_mem_drop hn)

private theorem l13bt_w5439_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5439 ∉ n.outs := by
  intro n hn
  exact l13bt_weights_not_written.2.2.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l13bt_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(563, 5414), (562, 8201), (562, 5409), (562, 5410), (562, 5412), (562, 5413), (566, 5429), (565, 5428), (567, 5431), (566, 5429), (568, 5432), (567, 5431), (569, 5433), (568, 5419), (568, 5432), (570, 5434), (569, 5414), (569, 5433), (571, 5435), (570, 5434), (572, 5436), (571, 8190), (571, 5435), (573, 8217), (573, 8221), (572, 5436), (574, 5438), (573, 8217), (575, 5440), (574, 5438)]) :
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
private theorem l13bt_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1187, 9913), (1186, 16086), (1186, 9903), (1186, 9905), (1186, 9909), (1186, 9911), (1186, 9910), (1186, 9912), (1190, 9914), (1189, 16109), (1189, 9904), (1189, 9906), (1189, 9909), (1189, 9910), (1189, 9911), (1189, 9912), (1193, 9967), (1192, 9965), (1194, 9968), (1193, 9966), (1195, 9973), (1194, 9967), (1196, 9974), (1195, 9968), (1197, 9983), (1196, 9973), (1198, 9984), (1197, 9974), (1199, 9987), (1198, 9927), (1198, 9983), (1200, 9988), (1199, 9928), (1199, 9984), (1201, 9991), (1200, 9913), (1200, 9987), (1202, 9992), (1201, 9914), (1201, 9988), (1203, 9997), (1202, 9991), (1204, 9998), (1203, 9992), (1205, 10001), (1204, 16067), (1204, 9997), (1206, 10002), (1205, 16075), (1205, 9998), (1207, 16125), (1207, 16129), (1206, 10001), (1208, 16133), (1208, 16137), (1207, 10002), (1209, 10005), (1208, 16125), (1210, 10006), (1209, 16133), (1211, 10007), (1210, 10005), (1212, 10008), (1211, 10006)]) :
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
private theorem l13bt_sm_leaf_not_written (tid : Nat)
    (h : tid ∈ [5412, 5413]) : ∀ n ∈ sm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l13bt_pm_leaf_not_written (tid : Nat)
    (h : tid ∈ [9909, 9910, 9911, 9912]) : ∀ n ∈ pm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> native_decide +revert

private theorem l13bt_sm_leaf (initSM : Store) (tid : Nat) (h : tid ∈ [5412, 5413]) :
    denoteGraphDistributedFaithful sm initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
    layer1_sm_nodes_nonempty (l13bt_sm_leaf_not_written tid h)

private theorem l13bt_pm_leaf (initPM : Store) (tid : Nat)
    (h : tid ∈ [9909, 9910, 9911, 9912]) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty (l13bt_pm_leaf_not_written tid h)

private theorem l13bt_pmFinal (initPM : Store) (tid : Tid)
    (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty hw

/-! ### Node reductions: MoE expert 5414 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_sm5414 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5414 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm initSM 8201)
        (denoteGraphDistributedFaithful sm initSM 5409)
        (denoteGraphDistributedFaithful sm initSM 5410)
        [denoteGraphDistributedFaithful sm initSM 5412]
        [denoteGraphDistributedFaithful sm initSM 5413]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l13bt_reduce5 sm initSM 562 l13btSmMoE5414
    8201 5409 5410 5412 5413 5414
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2] 64 8
      (((10 : Nat) : Scalar)))
    (by native_decide) l13bt_sm_node_facts.1 ?_
    (l13bt_nonempty_sm 563) (l13bt_sm_not_written 563 5414 (by decide))
    (l13bt_nonempty_sm 562) (l13bt_sm_not_written 562 8201 (by decide))
    (l13bt_sm_not_written 562 5409 (by decide))
    (l13bt_sm_not_written 562 5410 (by decide))
    (l13bt_sm_not_written 562 5412 (by decide))
    (l13bt_sm_not_written 562 5413 (by decide))
  intro s
  have hb := l13bt_buddy_facts.1
  unfold l13btSmMoE5414 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm s 0 8201 5409 5410 5412 5413 5414 [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9913 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9913 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16086)
        (denoteGraphDistributedFaithful pm initPM 9903)
        (denoteGraphDistributedFaithful pm initPM 9905)
        [denoteGraphDistributedFaithful pm initPM 9909,
         denoteGraphDistributedFaithful pm initPM 9910]
        [denoteGraphDistributedFaithful pm initPM 9911,
         denoteGraphDistributedFaithful pm initPM 9912]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l13bt_reduce7 pm initPM 1186 l13btPmMoE9913
    16086 9903 9905 9909 9911 9910 9912 9913
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l13bt_pm_node_facts.1 ?_
    (l13bt_nonempty_pm 1187) (l13bt_pm_not_written 1187 9913 (by decide))
    (l13bt_nonempty_pm 1186) (l13bt_pm_not_written 1186 16086 (by decide))
    (l13bt_pm_not_written 1186 9903 (by decide))
    (l13bt_pm_not_written 1186 9905 (by decide))
    (l13bt_pm_not_written 1186 9909 (by decide))
    (l13bt_pm_not_written 1186 9911 (by decide))
    (l13bt_pm_not_written 1186 9910 (by decide))
    (l13bt_pm_not_written 1186 9912 (by decide))
  intro s
  have hb := l13bt_buddy_facts.2.1
  unfold l13btPmMoE9913 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 0 16086 9903 9905 9909 9911 9913 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9914 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9914 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16109)
        (denoteGraphDistributedFaithful pm initPM 9904)
        (denoteGraphDistributedFaithful pm initPM 9906)
        [denoteGraphDistributedFaithful pm initPM 9909,
         denoteGraphDistributedFaithful pm initPM 9910]
        [denoteGraphDistributedFaithful pm initPM 9911,
         denoteGraphDistributedFaithful pm initPM 9912]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l13bt_reduce7 pm initPM 1189 l13btPmMoE9914
    16109 9904 9906 9909 9910 9911 9912 9914
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l13bt_pm_node_facts.2.1 ?_
    (l13bt_nonempty_pm 1190) (l13bt_pm_not_written 1190 9914 (by decide))
    (l13bt_nonempty_pm 1189) (l13bt_pm_not_written 1189 16109 (by decide))
    (l13bt_pm_not_written 1189 9904 (by decide))
    (l13bt_pm_not_written 1189 9906 (by decide))
    (l13bt_pm_not_written 1189 9909 (by decide))
    (l13bt_pm_not_written 1189 9910 (by decide))
    (l13bt_pm_not_written 1189 9911 (by decide))
    (l13bt_pm_not_written 1189 9912 (by decide))
  intro s
  have hb := l13bt_buddy_facts.2.2
  unfold l13btPmMoE9914 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 1 16109 9904 9906 9910 9912 9914 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

/-! ### Node reductions: reshape 5429 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_sm5429 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5429 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5428) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 565 l13btSmResh5429
    5428 5429 (fun x => fw_view [4096,512] x)
    (by native_decide) l13bt_sm_node_facts.2.1 ?_
    (l13bt_nonempty_sm 566) (l13bt_sm_not_written 566 5429 (by decide))
    (l13bt_nonempty_sm 565) (l13bt_sm_not_written 565 5428 (by decide))
  intro s
  unfold l13btSmResh5429
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5428 5429 [4096,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9967 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9967 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 9965) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1192 l13btPmResh9967
    9965 9967 (fun x => fw_view [2048,512] x)
    (by native_decide) l13bt_pm_node_facts.2.2.1 ?_
    (l13bt_nonempty_pm 1193) (l13bt_pm_not_written 1193 9967 (by decide))
    (l13bt_nonempty_pm 1192) (l13bt_pm_not_written 1192 9965 (by decide))
  intro s
  unfold l13btPmResh9967
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 9965 9967 [2048,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9968 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9968 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 9966) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1193 l13btPmResh9968
    9966 9968 (fun x => fw_view [2048,512] x)
    (by native_decide) l13bt_pm_node_facts.2.2.2.1 ?_
    (l13bt_nonempty_pm 1194) (l13bt_pm_not_written 1194 9968 (by decide))
    (l13bt_nonempty_pm 1193) (l13bt_pm_not_written 1193 9966 (by decide))
  intro s
  unfold l13btPmResh9968
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 9966 9968 [2048,512]

/-! ### Node reductions: down-projection 5431 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_sm5431 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5431 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5429)
        (denoteGraphDistributedFaithful sm initSM 5430) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 566 l13btSmMPL5431
    5429 5430 5431 fw_linear
    (by native_decide) l13bt_sm_node_facts.2.2.1 ?_
    (l13bt_nonempty_sm 567) (l13bt_sm_not_written 567 5431 (by decide))
    (l13bt_nonempty_sm 566) (l13bt_sm_not_written 566 5429 (by decide))
    (l13bt_w5430_sm_drop 566)
  intro s
  unfold l13btSmMPL5431
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5429 5430 5431

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9973 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9973 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9967)
        (denoteGraphDistributedFaithful pm initPM 5430) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1194 l13btPmMPL9973
    9967 5430 9973 fw_linear
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1195) (l13bt_pm_not_written 1195 9973 (by decide))
    (l13bt_nonempty_pm 1194) (l13bt_pm_not_written 1194 9967 (by decide))
    (l13bt_w5430_pm_drop 1194)
  intro s
  unfold l13btPmMPL9973
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 9967 5430 9973

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9974 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9974 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9968)
        (denoteGraphDistributedFaithful pm initPM 5430) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1195 l13btPmMPL9974
    9968 5430 9974 fw_linear
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1196) (l13bt_pm_not_written 1196 9974 (by decide))
    (l13bt_nonempty_pm 1195) (l13bt_pm_not_written 1195 9968 (by decide))
    (l13bt_w5430_pm_drop 1195)
  intro s
  unfold l13btPmMPL9974
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 9968 5430 9974

/-! ### Node reductions: view 5432 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_sm5432 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5432 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 5431) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 567 l13btSmView5432
    5431 5432 (fun x => fw_view [4096,1024] x)
    (by native_decide) l13bt_sm_node_facts.2.2.2.1 ?_
    (l13bt_nonempty_sm 568) (l13bt_sm_not_written 568 5432 (by decide))
    (l13bt_nonempty_sm 567) (l13bt_sm_not_written 567 5431 (by decide))
  intro s
  unfold l13btSmView5432
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5431 5432

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9983 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9983 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 9973) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1196 l13btPmView9983
    9973 9983 (fun x => fw_view [2048,1024] x)
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1197) (l13bt_pm_not_written 1197 9983 (by decide))
    (l13bt_nonempty_pm 1196) (l13bt_pm_not_written 1196 9973 (by decide))
  intro s
  unfold l13btPmView9983
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 9973 9983

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9984 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9984 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 9974) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1197 l13btPmView9984
    9974 9984 (fun x => fw_view [2048,1024] x)
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1198) (l13bt_pm_not_written 1198 9984 (by decide))
    (l13bt_nonempty_pm 1197) (l13bt_pm_not_written 1197 9974 (by decide))
  intro s
  unfold l13btPmView9984
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 9974 9984

/-! ### Node reductions: gated multiply 5433 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_sm5433 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5433 =
      elemwiseMul (denoteGraphDistributedFaithful sm initSM 5419)
        (denoteGraphDistributedFaithful sm initSM 5432) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 568 l13btSmMul5433
    5419 5432 5433 elemwiseMul
    (by native_decide) l13bt_sm_node_facts.2.2.2.2.1 ?_
    (l13bt_nonempty_sm 569) (l13bt_sm_not_written 569 5433 (by decide))
    (l13bt_nonempty_sm 568) (l13bt_sm_not_written 568 5419 (by decide))
    (l13bt_sm_not_written 568 5432 (by decide))
  intro s
  unfold l13btSmMul5433
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm s 0 5419 5432 5433

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9987 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9987 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 9927)
        (denoteGraphDistributedFaithful pm initPM 9983) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1198 l13btPmMul9987
    9927 9983 9987 elemwiseMul
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1199) (l13bt_pm_not_written 1199 9987 (by decide))
    (l13bt_nonempty_pm 1198) (l13bt_pm_not_written 1198 9927 (by decide))
    (l13bt_pm_not_written 1198 9983 (by decide))
  intro s
  unfold l13btPmMul9987
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 0 9927 9983 9987

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9988 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9988 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 9928)
        (denoteGraphDistributedFaithful pm initPM 9984) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1199 l13btPmMul9988
    9928 9984 9988 elemwiseMul
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1200) (l13bt_pm_not_written 1200 9988 (by decide))
    (l13bt_nonempty_pm 1199) (l13bt_pm_not_written 1199 9928 (by decide))
    (l13bt_pm_not_written 1199 9984 (by decide))
  intro s
  unfold l13btPmMul9988
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 1 9928 9984 9988

/-! ### Node reductions: MoE join 5434 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_sm5434 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5434 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 5414)
        (denoteGraphDistributedFaithful sm initSM 5433) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 569 l13btSmAdd5434
    5414 5433 5434 elemwiseAdd
    (by native_decide) l13bt_sm_node_facts.2.2.2.2.2.1 ?_
    (l13bt_nonempty_sm 570) (l13bt_sm_not_written 570 5434 (by decide))
    (l13bt_nonempty_sm 569) (l13bt_sm_not_written 569 5414 (by decide))
    (l13bt_sm_not_written 569 5433 (by decide))
  intro s
  unfold l13btSmAdd5434
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 5414 5433 5434

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9991 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9991 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 9913)
        (denoteGraphDistributedFaithful pm initPM 9987) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1200 l13btPmAdd9991
    9913 9987 9991 elemwiseAdd
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1201) (l13bt_pm_not_written 1201 9991 (by decide))
    (l13bt_nonempty_pm 1200) (l13bt_pm_not_written 1200 9913 (by decide))
    (l13bt_pm_not_written 1200 9987 (by decide))
  intro s
  unfold l13btPmAdd9991
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 9913 9987 9991

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9992 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9992 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 9914)
        (denoteGraphDistributedFaithful pm initPM 9988) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1201 l13btPmAdd9992
    9914 9988 9992 elemwiseAdd
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1202) (l13bt_pm_not_written 1202 9992 (by decide))
    (l13bt_nonempty_pm 1201) (l13bt_pm_not_written 1201 9914 (by decide))
    (l13bt_pm_not_written 1201 9988 (by decide))
  intro s
  unfold l13btPmAdd9992
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 9914 9988 9992

/-! ### Node reductions: float 5435 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_sm5435 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5435 =
      denoteGraphDistributedFaithful sm initSM 5434 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 570 l13btSmFloat5435
    5434 5435 (fun x => x)
    (by native_decide) l13bt_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_sm 571) (l13bt_sm_not_written 571 5435 (by decide))
    (l13bt_nonempty_sm 570) (l13bt_sm_not_written 570 5434 (by decide))
  intro s
  unfold l13btSmFloat5435
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 5434 5435 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9997 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9997 =
      denoteGraphDistributedFaithful pm initPM 9991 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1202 l13btPmFloat9997
    9991 9997 (fun x => x)
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1203) (l13bt_pm_not_written 1203 9997 (by decide))
    (l13bt_nonempty_pm 1202) (l13bt_pm_not_written 1202 9991 (by decide))
  intro s
  unfold l13btPmFloat9997
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 9991 9997 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm9998 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9998 =
      denoteGraphDistributedFaithful pm initPM 9992 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1203 l13btPmFloat9998
    9992 9998 (fun x => x)
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1204) (l13bt_pm_not_written 1204 9998 (by decide))
    (l13bt_nonempty_pm 1203) (l13bt_pm_not_written 1203 9992 (by decide))
  intro s
  unfold l13btPmFloat9998
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 9992 9998 []

/-! ### Node reductions: residual join 5436 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_sm5436 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5436 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8190)
        (denoteGraphDistributedFaithful sm initSM 5435) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 571 l13btSmAdd5436
    8190 5435 5436 elemwiseAdd
    (by native_decide) l13bt_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_sm 572) (l13bt_sm_not_written 572 5436 (by decide))
    (l13bt_nonempty_sm 571) (l13bt_sm_not_written 571 8190 (by decide))
    (l13bt_sm_not_written 571 5435 (by decide))
  intro s
  unfold l13btSmAdd5436
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8190 5435 5436

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm10001 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10001 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16067)
        (denoteGraphDistributedFaithful pm initPM 9997) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1204 l13btPmAdd10001
    16067 9997 10001 elemwiseAdd
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1205) (l13bt_pm_not_written 1205 10001 (by decide))
    (l13bt_nonempty_pm 1204) (l13bt_pm_not_written 1204 16067 (by decide))
    (l13bt_pm_not_written 1204 9997 (by decide))
  intro s
  unfold l13btPmAdd10001
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16067 9997 10001

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm10002 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10002 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16075)
        (denoteGraphDistributedFaithful pm initPM 9998) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1205 l13btPmAdd10002
    16075 9998 10002 elemwiseAdd
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1206) (l13bt_pm_not_written 1206 10002 (by decide))
    (l13bt_nonempty_pm 1205) (l13bt_pm_not_written 1205 16075 (by decide))
    (l13bt_pm_not_written 1205 9998 (by decide))
  intro s
  unfold l13btPmAdd10002
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16075 9998 10002

/-! ### Node reductions: 2-way multiref off 5436 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_sm8217 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8217 =
      denoteGraphDistributedFaithful sm initSM 5436 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 572 l13btSmMref5436
    5436 8217 (fun x => x)
    (by native_decide) l13bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_sm 573) (l13bt_sm_not_written 573 8217 (by decide))
    (l13bt_nonempty_sm 572) (l13bt_sm_not_written 572 5436 (by decide))
  intro s
  unfold l13btSmMref5436
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5436 8217 8221

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_sm8221 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8221 =
      denoteGraphDistributedFaithful sm initSM 5436 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 572 l13btSmMref5436
    5436 8221 (fun x => x)
    (by native_decide) l13bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_sm 573) (l13bt_sm_not_written 573 8221 (by decide))
    (l13bt_nonempty_sm 572) (l13bt_sm_not_written 572 5436 (by decide))
  intro s
  unfold l13btSmMref5436
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5436 8217 8221 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm16125 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16125 =
      denoteGraphDistributedFaithful pm initPM 10001 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1206 l13btPmMref10001
    10001 16125 (fun x => x)
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1207) (l13bt_pm_not_written 1207 16125 (by decide))
    (l13bt_nonempty_pm 1206) (l13bt_pm_not_written 1206 10001 (by decide))
  intro s
  unfold l13btPmMref10001
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 10001 16125 16129

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm16129 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16129 =
      denoteGraphDistributedFaithful pm initPM 10001 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1206 l13btPmMref10001
    10001 16129 (fun x => x)
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1207) (l13bt_pm_not_written 1207 16129 (by decide))
    (l13bt_nonempty_pm 1206) (l13bt_pm_not_written 1206 10001 (by decide))
  intro s
  unfold l13btPmMref10001
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 10001 16125 16129 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm16133 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16133 =
      denoteGraphDistributedFaithful pm initPM 10002 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1207 l13btPmMref10002
    10002 16133 (fun x => x)
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1208) (l13bt_pm_not_written 1208 16133 (by decide))
    (l13bt_nonempty_pm 1207) (l13bt_pm_not_written 1207 10002 (by decide))
  intro s
  unfold l13btPmMref10002
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 10002 16133 16137

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm16137 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16137 =
      denoteGraphDistributedFaithful pm initPM 10002 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1207 l13btPmMref10002
    10002 16137 (fun x => x)
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1208) (l13bt_pm_not_written 1208 16137 (by decide))
    (l13bt_nonempty_pm 1207) (l13bt_pm_not_written 1207 10002 (by decide))
  intro s
  unfold l13btPmMref10002
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 10002 16133 16137 (by decide)

/-! ### Node reductions: RMSNorm 5438 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_sm5438 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5438 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8217)
        (denoteGraphDistributedFaithful sm initSM 5437) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 573 l13btSmRms5438
    8217 5437 5438 fw_rms_norm
    (by native_decide) l13bt_sm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_sm 574) (l13bt_sm_not_written 574 5438 (by decide))
    (l13bt_nonempty_sm 573) (l13bt_sm_not_written 573 8217 (by decide))
    (l13bt_w5437_sm_drop 573)
  intro s
  unfold l13btSmRms5438
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8217 5437 5438

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm10005 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10005 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16125)
        (denoteGraphDistributedFaithful pm initPM 5437) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1208 l13btPmRms10005
    16125 5437 10005 fw_rms_norm
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1209) (l13bt_pm_not_written 1209 10005 (by decide))
    (l13bt_nonempty_pm 1208) (l13bt_pm_not_written 1208 16125 (by decide))
    (l13bt_w5437_pm_drop 1208)
  intro s
  unfold l13btPmRms10005
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16125 5437 10005

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm10006 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10006 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16133)
        (denoteGraphDistributedFaithful pm initPM 5437) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1209 l13btPmRms10006
    16133 5437 10006 fw_rms_norm
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1210) (l13bt_pm_not_written 1210 10006 (by decide))
    (l13bt_nonempty_pm 1209) (l13bt_pm_not_written 1209 16133 (by decide))
    (l13bt_w5437_pm_drop 1209)
  intro s
  unfold l13btPmRms10006
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16133 5437 10006

/-! ### Node reductions: per-head Q projection 5440 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_sm5440 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5440 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 5438)
        (denoteGraphDistributedFaithful sm initSM 5439) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 574 l13btSmPhl5440
    5438 5439 5440 fw_per_head_linear
    (by native_decide) l13bt_sm_node_facts.2.2.2.2.2.2.2.2.2.2 ?_
    (l13bt_nonempty_sm 575) (l13bt_sm_not_written 575 5440 (by decide))
    (l13bt_nonempty_sm 574) (l13bt_sm_not_written 574 5438 (by decide))
    (l13bt_w5439_sm_drop 574)
  intro s
  unfold l13btSmPhl5440
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 5438 5439 5440 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm10007 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10007 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 10005)
        (denoteGraphDistributedFaithful pm initPM 5439) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1210 l13btPmPhl10007
    10005 5439 10007 fw_per_head_linear
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13bt_nonempty_pm 1211) (l13bt_pm_not_written 1211 10007 (by decide))
    (l13bt_nonempty_pm 1210) (l13bt_pm_not_written 1210 10005 (by decide))
    (l13bt_w5439_pm_drop 1210)
  intro s
  unfold l13btPmPhl10007
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 0 10005 5439 10007 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_red_pm10008 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10008 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 10006)
        (denoteGraphDistributedFaithful pm initPM 5439) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1211 l13btPmPhl10008
    10006 5439 10008 fw_per_head_linear
    (by native_decide) l13bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l13bt_nonempty_pm 1212) (l13bt_pm_not_written 1212 10008 (by decide))
    (l13bt_nonempty_pm 1211) (l13bt_pm_not_written 1211 10006 (by decide))
    (l13bt_w5439_pm_drop 1211)
  intro s
  unfold l13btPmPhl10008
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 10006 5439 10008 []

/-! ### Shared helpers: weight transport and cu identification -/

set_option maxRecDepth 1000000 in
private theorem l13bt_weight_bridge (initSM initPM : Store)
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
private theorem l13bt_weight_eq (initSM initPM : Store)
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
private theorem l13bt_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  rw [l13bt_pmFinal initPM W hpw]
  exact hPM W sh hmem

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_cu_eq (initPM : Store)
    (hValues : InputValueClassesHold pmInputValueClasses initPM) :
    denoteGraphDistributedFaithful pm initPM 5345 =
      denoteGraphDistributedFaithful pm initPM 5394 := by
  rw [l13bt_pmFinal initPM 5345 (fun n hn => (l13bt_cu_not_written n hn).1),
    l13bt_pmFinal initPM 5394 (fun n hn => (l13bt_cu_not_written n hn).2)]
  exact hValues.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
    (by native_decide) (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13bt_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5394) = [0, 2 * 2048] := by
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5394).shape = [2] := by
    rw [l13bt_pmFinal initPM 5394 (fun n hn => (l13bt_cu_not_written n hn).2)]
    exact hPM 5394 [2] (by native_decide)
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5394)).length = 2 := by
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
-- Faithful zigzag relation for generated goal 5414 (block-1 MoE expert layer).
theorem recon_zigzagGoal_5414_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5414)
      (denoteGraphDistributedFaithful pm initPM 9913)
      (denoteGraphDistributedFaithful pm initPM 9914)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hX := recon_zigzagGoal_8201_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRP := recon_zigzagGoal_5409_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRM := recon_zigzagGoal_5410_faithful initSM initPM hSM hPM hInit hValues hCu
  have hcu := l13bt_cu_eq initPM hValues.2
  have hdec := l13bt_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8201)
      (denoteGraphDistributedFaithful pm initPM 16086)
      (denoteGraphDistributedFaithful pm initPM 16109)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5409)
      (denoteGraphDistributedFaithful pm initPM 9903)
      (denoteGraphDistributedFaithful pm initPM 9904)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5410)
      (denoteGraphDistributedFaithful pm initPM 9905)
      (denoteGraphDistributedFaithful pm initPM 9906)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 5412 = allGatherPrimDimN 0 2 0 [initPM 9909, initPM 9910] :=
    l13bt_weight_bridge initSM initPM hInit initGoal_5412 (by native_decide)
      5412 9909 9910 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5413 = allGatherPrimDimN 0 2 0 [initPM 9911, initPM 9912] :=
    l13bt_weight_bridge initSM initPM hInit initGoal_5413 (by native_decide)
      5413 9911 9912 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5412).shape = [64, 1024, 1024] :=
    hSM 5412 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5413).shape = [64, 1024, 512] :=
    hSM 5413 [64, 1024, 512] (by native_decide)
  rw [l13bt_red_sm5414 initSM, l13bt_red_pm9913 initPM, l13bt_red_pm9914 initPM]
  rw [l13bt_sm_leaf initSM 5412 (by decide), l13bt_sm_leaf initSM 5413 (by decide),
    l13bt_pm_leaf initPM 9909 (by decide), l13bt_pm_leaf initPM 9910 (by decide),
    l13bt_pm_leaf initPM 9911 (by decide), l13bt_pm_leaf initPM 9912 (by decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5412) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5413) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 9909, initPM 9910])
    (allGatherPrimDimN 0 2 0 [initPM 9911, initPM 9912])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5429 (`FW_reshape`).
theorem recon_zigzagGoal_5429_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5429)
      (denoteGraphDistributedFaithful pm initPM 9967)
      (denoteGraphDistributedFaithful pm initPM 9968)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 512] [2048, 512] := by
  have hparent := recon_zigzagGoal_5428_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13bt_red_sm5429 initSM, l13bt_red_pm9967 initPM, l13bt_red_pm9968 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5431 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5431_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5431)
      (denoteGraphDistributedFaithful pm initPM 9973)
      (denoteGraphDistributedFaithful pm initPM 9974)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5429_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5430 =
      denoteGraphDistributedFaithful pm initPM 5430 :=
    l13bt_weight_eq initSM initPM hInit 5430 initGoal_5430 (by native_decide)
      rfl rfl rfl rfl
      l13bt_weights_not_written.1.1 l13bt_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5430).shape = [1024, 512] :=
    l13bt_pm_weight_shape initPM hPM 5430 [1024, 512] (by native_decide)
      l13bt_weights_not_written.2.1
  rw [l13bt_red_sm5431 initSM, l13bt_red_pm9973 initPM, l13bt_red_pm9974 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5432 (`FW_view`).
theorem recon_zigzagGoal_5432_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5432)
      (denoteGraphDistributedFaithful pm initPM 9983)
      (denoteGraphDistributedFaithful pm initPM 9984)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5431_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13bt_red_sm5432 initSM, l13bt_red_pm9983 initPM, l13bt_red_pm9984 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5433 (broadcast `FW_mul`).
theorem recon_zigzagGoal_5433_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5433)
      (denoteGraphDistributedFaithful pm initPM 9987)
      (denoteGraphDistributedFaithful pm initPM 9988)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5419_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5432_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5419)
      (denoteGraphDistributedFaithful pm initPM 9927)
      (denoteGraphDistributedFaithful pm initPM 9928)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 1] [2048, 1] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5432)
      (denoteGraphDistributedFaithful pm initPM 9983)
      (denoteGraphDistributedFaithful pm initPM 9984)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l13bt_red_sm5433 initSM, l13bt_red_pm9987 initPM, l13bt_red_pm9988 initPM]
  exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5434 (`FW_add`, MoE join).
theorem recon_zigzagGoal_5434_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5434)
      (denoteGraphDistributedFaithful pm initPM 9991)
      (denoteGraphDistributedFaithful pm initPM 9992)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5414_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5433_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5414)
      (denoteGraphDistributedFaithful pm initPM 9913)
      (denoteGraphDistributedFaithful pm initPM 9914)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5433)
      (denoteGraphDistributedFaithful pm initPM 9987)
      (denoteGraphDistributedFaithful pm initPM 9988)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l13bt_red_sm5434 initSM, l13bt_red_pm9991 initPM, l13bt_red_pm9992 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5435 (`FW_float`, identity cast).
theorem recon_zigzagGoal_5435_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5435)
      (denoteGraphDistributedFaithful pm initPM 9997)
      (denoteGraphDistributedFaithful pm initPM 9998)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5434_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13bt_red_sm5435 initSM, l13bt_red_pm9997 initPM, l13bt_red_pm9998 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5436 (`FW_add`, residual join).
theorem recon_zigzagGoal_5436_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5436)
      (denoteGraphDistributedFaithful pm initPM 10001)
      (denoteGraphDistributedFaithful pm initPM 10002)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8190_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5435_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8190)
      (denoteGraphDistributedFaithful pm initPM 16067)
      (denoteGraphDistributedFaithful pm initPM 16075)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5435)
      (denoteGraphDistributedFaithful pm initPM 9997)
      (denoteGraphDistributedFaithful pm initPM 9998)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l13bt_red_sm5436 initSM, l13bt_red_pm10001 initPM, l13bt_red_pm10002 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8217 (multiref position 0 off 5436).
theorem recon_zigzagGoal_8217_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8217)
      (denoteGraphDistributedFaithful pm initPM 16125)
      (denoteGraphDistributedFaithful pm initPM 16133)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5436_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13bt_red_sm8217 initSM, l13bt_red_pm16125 initPM, l13bt_red_pm16133 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 8221 (multiref position 1
-- off 5436): the cross-layer residual bypass consumed by block 2's `FW_add`.
theorem recon_zigzagGoal_8221_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8221)
      (denoteGraphDistributedFaithful pm initPM 16129)
      (denoteGraphDistributedFaithful pm initPM 16137)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5436_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13bt_red_sm8221 initSM, l13bt_red_pm16129 initPM, l13bt_red_pm16137 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5438 (`FW_rms_norm`).
theorem recon_zigzagGoal_5438_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5438)
      (denoteGraphDistributedFaithful pm initPM 10005)
      (denoteGraphDistributedFaithful pm initPM 10006)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_8217_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5437 =
      denoteGraphDistributedFaithful pm initPM 5437 :=
    l13bt_weight_eq initSM initPM hInit 5437 initGoal_5437 (by native_decide)
      rfl rfl rfl rfl
      l13bt_weights_not_written.1.2.1 l13bt_weights_not_written.2.2.1
  rw [l13bt_red_sm5438 initSM, l13bt_red_pm10005 initPM, l13bt_red_pm10006 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 5440
-- (`FW_per_head_mix_precision_linear`): the per-head Q projection feeding block 2's
-- zigzag attention entry.
theorem recon_zigzagGoal_5440_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5440)
      (denoteGraphDistributedFaithful pm initPM 10007)
      (denoteGraphDistributedFaithful pm initPM 10008)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 16, 64] [2048, 16, 64] := by
  have hparent := recon_zigzagGoal_5438_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5439 =
      denoteGraphDistributedFaithful pm initPM 5439 :=
    l13bt_weight_eq initSM initPM hInit 5439 initGoal_5439 (by native_decide)
      rfl rfl rfl rfl
      l13bt_weights_not_written.1.2.2 l13bt_weights_not_written.2.2.2
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5439).shape = [16, 64, 1024] :=
    l13bt_pm_weight_shape initPM hPM 5439 [16, 64, 1024] (by native_decide)
      l13bt_weights_not_written.2.2.2
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5438)
      (denoteGraphDistributedFaithful pm initPM 10005)
      (denoteGraphDistributedFaithful pm initPM 10006)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l13bt_red_sm5440 initSM, l13bt_red_pm10007 initPM, l13bt_red_pm10008 initPM, hw]
  exact Zigzag2Rel.per_head_linear 2048 1024 16 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
