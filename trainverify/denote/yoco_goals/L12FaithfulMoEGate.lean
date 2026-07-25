/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L12FaithfulMoEBranch
import denote.yoco_goals.ZigzagBroadcastMul

/-!
# Faithful zigzag relations for the MoE gate down-projection + broadcast multiply

* SM 530 `FW_reshape [5379] → [5380]` params `[4096, 512]`   (PM 1122 / 1123 → 9795 / 9796)
* SM 531 `FW_mix_precision_linear [5380, 5381] → [5382]`     (PM 1124 / 1125 → 9801 / 9802)
* SM 532 `FW_view [5382] → [5383]` params `[4096, 1024]`     (PM 1126 / 1127 → 9811 / 9812)
* SM 533 `FW_mul [5370, 5383] → [5384]`                      (PM 1128 / 1129 → 9815 / 9816)

`5381` (the `[1024, 512]` down-projection weight) is replicated (`initGoal_5381.tps`
is the singleton `5381`), so it is shared verbatim between SM and PM.

Node 533 is a **broadcast** multiply (`[4096,1] × [4096,1024]`), handled by
`Zigzag2Rel.mul_broadcast_col1`, not the equal-shape `Zigzag2Rel.mul`.

Every theorem below takes literally the same five parameters as its parent
(`recon_zigzagGoal_5379_faithful` / `_5370_`); no new hypotheses are introduced.
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

/-! ### Node literals -/

private def l12mgSmResh5380 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5379], outs := [5380], params := [4096,512] }
private def l12mgSmMPL5382 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5380,5381], outs := [5382] }
private def l12mgSmView5383 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5382], outs := [5383], params := [4096,1024] }
private def l12mgSmMul5384 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5370,5383], outs := [5384] }

private def l12mgPmResh9795 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9793], outs := [9795], params := [2048,512] }
private def l12mgPmResh9796 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9794], outs := [9796], params := [2048,512] }
private def l12mgPmMPL9801 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9795,5381], outs := [9801] }
private def l12mgPmMPL9802 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9796,5381], outs := [9802] }
private def l12mgPmView9811 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9801], outs := [9811], params := [2048,1024] }
private def l12mgPmView9812 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9802], outs := [9812], params := [2048,1024] }
private def l12mgPmMul9815 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [9755,9811], outs := [9815] }
private def l12mgPmMul9816 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [9756,9812], outs := [9816] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l12mg_sm_node_facts :
    sm.nodes[530]'(by native_decide) = l12mgSmResh5380 ∧
    sm.nodes[531]'(by native_decide) = l12mgSmMPL5382 ∧
    sm.nodes[532]'(by native_decide) = l12mgSmView5383 ∧
    sm.nodes[533]'(by native_decide) = l12mgSmMul5384 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12mg_pm_node_facts :
    pm.nodes[1122]'(by native_decide) = l12mgPmResh9795 ∧
    pm.nodes[1123]'(by native_decide) = l12mgPmResh9796 ∧
    pm.nodes[1124]'(by native_decide) = l12mgPmMPL9801 ∧
    pm.nodes[1125]'(by native_decide) = l12mgPmMPL9802 ∧
    pm.nodes[1126]'(by native_decide) = l12mgPmView9811 ∧
    pm.nodes[1127]'(by native_decide) = l12mgPmView9812 ∧
    pm.nodes[1128]'(by native_decide) = l12mgPmMul9815 ∧
    pm.nodes[1129]'(by native_decide) = l12mgPmMul9816 := by
  native_decide

private theorem l12mg_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l12mg_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12mg_w5381_not_written :
    (∀ n ∈ sm.nodes, 5381 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5381 ∉ n.outs) := by
  native_decide

private theorem l12mg_w5381_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5381 ∉ n.outs := by
  intro n hn
  exact l12mg_w5381_not_written.1 n (List.mem_of_mem_drop hn)

private theorem l12mg_w5381_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5381 ∉ n.outs := by
  intro n hn
  exact l12mg_w5381_not_written.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12mg_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(531, 5380), (530, 5379), (532, 5382), (531, 5380), (533, 5383), (532, 5382), (534, 5384), (533, 5370), (533, 5383)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12mg_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1123, 9795), (1122, 9793), (1124, 9796), (1123, 9794), (1125, 9801), (1124, 9795), (1126, 9802), (1125, 9796), (1127, 9811), (1126, 9801), (1128, 9812), (1127, 9802), (1129, 9815), (1128, 9755), (1128, 9811), (1130, 9816), (1129, 9756), (1129, 9812)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_red_sm5380 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5380 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5379) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 530 l12mgSmResh5380
    5379 5380 (fun x => fw_view [4096,512] x)
    (by native_decide) l12mg_sm_node_facts.1 ?_
    (l12mg_nonempty_sm 531) (l12mg_sm_not_written 531 5380 (by decide))
    (l12mg_nonempty_sm 530) (l12mg_sm_not_written 530 5379 (by decide))
  intro s
  unfold l12mgSmResh5380
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5379 5380 [4096,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_red_pm9795 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9795 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 9793) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1122 l12mgPmResh9795
    9793 9795 (fun x => fw_view [2048,512] x)
    (by native_decide) l12mg_pm_node_facts.1 ?_
    (l12mg_nonempty_pm 1123) (l12mg_pm_not_written 1123 9795 (by decide))
    (l12mg_nonempty_pm 1122) (l12mg_pm_not_written 1122 9793 (by decide))
  intro s
  unfold l12mgPmResh9795
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 9793 9795 [2048,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_red_pm9796 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9796 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 9794) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1123 l12mgPmResh9796
    9794 9796 (fun x => fw_view [2048,512] x)
    (by native_decide) l12mg_pm_node_facts.2.1 ?_
    (l12mg_nonempty_pm 1124) (l12mg_pm_not_written 1124 9796 (by decide))
    (l12mg_nonempty_pm 1123) (l12mg_pm_not_written 1123 9794 (by decide))
  intro s
  unfold l12mgPmResh9796
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 9794 9796 [2048,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_red_sm5382 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5382 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5380)
        (denoteGraphDistributedFaithful sm initSM 5381) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 531 l12mgSmMPL5382
    5380 5381 5382 fw_linear
    (by native_decide) l12mg_sm_node_facts.2.1 ?_
    (l12mg_nonempty_sm 532) (l12mg_sm_not_written 532 5382 (by decide))
    (l12mg_nonempty_sm 531) (l12mg_sm_not_written 531 5380 (by decide))
    (l12mg_w5381_sm_drop 531)
  intro s
  unfold l12mgSmMPL5382
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5380 5381 5382

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_red_pm9801 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9801 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9795)
        (denoteGraphDistributedFaithful pm initPM 5381) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1124 l12mgPmMPL9801
    9795 5381 9801 fw_linear
    (by native_decide) l12mg_pm_node_facts.2.2.1 ?_
    (l12mg_nonempty_pm 1125) (l12mg_pm_not_written 1125 9801 (by decide))
    (l12mg_nonempty_pm 1124) (l12mg_pm_not_written 1124 9795 (by decide))
    (l12mg_w5381_pm_drop 1124)
  intro s
  unfold l12mgPmMPL9801
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 9795 5381 9801

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_red_pm9802 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9802 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9796)
        (denoteGraphDistributedFaithful pm initPM 5381) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1125 l12mgPmMPL9802
    9796 5381 9802 fw_linear
    (by native_decide) l12mg_pm_node_facts.2.2.2.1 ?_
    (l12mg_nonempty_pm 1126) (l12mg_pm_not_written 1126 9802 (by decide))
    (l12mg_nonempty_pm 1125) (l12mg_pm_not_written 1125 9796 (by decide))
    (l12mg_w5381_pm_drop 1125)
  intro s
  unfold l12mgPmMPL9802
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 9796 5381 9802

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_red_sm5383 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5383 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 5382) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 532 l12mgSmView5383
    5382 5383 (fun x => fw_view [4096,1024] x)
    (by native_decide) l12mg_sm_node_facts.2.2.1 ?_
    (l12mg_nonempty_sm 533) (l12mg_sm_not_written 533 5383 (by decide))
    (l12mg_nonempty_sm 532) (l12mg_sm_not_written 532 5382 (by decide))
  intro s
  unfold l12mgSmView5383
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5382 5383

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_red_pm9811 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9811 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 9801) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1126 l12mgPmView9811
    9801 9811 (fun x => fw_view [2048,1024] x)
    (by native_decide) l12mg_pm_node_facts.2.2.2.2.1 ?_
    (l12mg_nonempty_pm 1127) (l12mg_pm_not_written 1127 9811 (by decide))
    (l12mg_nonempty_pm 1126) (l12mg_pm_not_written 1126 9801 (by decide))
  intro s
  unfold l12mgPmView9811
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 9801 9811

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_red_pm9812 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9812 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 9802) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1127 l12mgPmView9812
    9802 9812 (fun x => fw_view [2048,1024] x)
    (by native_decide) l12mg_pm_node_facts.2.2.2.2.2.1 ?_
    (l12mg_nonempty_pm 1128) (l12mg_pm_not_written 1128 9812 (by decide))
    (l12mg_nonempty_pm 1127) (l12mg_pm_not_written 1127 9802 (by decide))
  intro s
  unfold l12mgPmView9812
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 9802 9812

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_red_sm5384 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5384 =
      elemwiseMul (denoteGraphDistributedFaithful sm initSM 5370)
        (denoteGraphDistributedFaithful sm initSM 5383) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 533 l12mgSmMul5384
    5370 5383 5384 elemwiseMul
    (by native_decide) l12mg_sm_node_facts.2.2.2 ?_
    (l12mg_nonempty_sm 534) (l12mg_sm_not_written 534 5384 (by decide))
    (l12mg_nonempty_sm 533) (l12mg_sm_not_written 533 5370 (by decide))
    (l12mg_sm_not_written 533 5383 (by decide))
  intro s
  unfold l12mgSmMul5384
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm s 0 5370 5383 5384

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_red_pm9815 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9815 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 9755)
        (denoteGraphDistributedFaithful pm initPM 9811) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1128 l12mgPmMul9815
    9755 9811 9815 elemwiseMul
    (by native_decide) l12mg_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l12mg_nonempty_pm 1129) (l12mg_pm_not_written 1129 9815 (by decide))
    (l12mg_nonempty_pm 1128) (l12mg_pm_not_written 1128 9755 (by decide))
    (l12mg_pm_not_written 1128 9811 (by decide))
  intro s
  unfold l12mgPmMul9815
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 0 9755 9811 9815

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_red_pm9816 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9816 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 9756)
        (denoteGraphDistributedFaithful pm initPM 9812) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1129 l12mgPmMul9816
    9756 9812 9816 elemwiseMul
    (by native_decide) l12mg_pm_node_facts.2.2.2.2.2.2.2 ?_
    (l12mg_nonempty_pm 1130) (l12mg_pm_not_written 1130 9816 (by decide))
    (l12mg_nonempty_pm 1129) (l12mg_pm_not_written 1129 9756 (by decide))
    (l12mg_pm_not_written 1129 9812 (by decide))
  intro s
  unfold l12mgPmMul9816
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 1 9756 9812 9816

/-! ### Replicated weight `5381` -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_w5381_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm initSM 5381 =
      denoteGraphDistributedFaithful pm initPM 5381 := by
  have h : initSM 5381 = initPM 5381 := by
    have hr := recon_weight initSM initPM hInit initGoal_5381 (by native_decide) 5381
      rfl rfl rfl rfl
    unfold denoteGraph at hr
    rw [foldl_applyNode_at_not_written sm sm.nodes initSM 5381 l12mg_w5381_not_written.1,
      foldl_applyNode_at_not_written pm pm.nodes initPM 5381 l12mg_w5381_not_written.2] at hr
    exact hr
  have e1 : denoteGraphDistributedFaithful sm initSM 5381 = initSM 5381 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5381
      layer1_sm_nodes_nonempty l12mg_w5381_not_written.1
  have e2 : denoteGraphDistributedFaithful pm initPM 5381 = initPM 5381 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5381
      layer1_pm_nodes_nonempty l12mg_w5381_not_written.2
  rw [e1, e2]; exact h

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mg_w5381_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5381).shape = [1024,512] := by
  have e2 : denoteGraphDistributedFaithful pm initPM 5381 = initPM 5381 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5381
      layer1_pm_nodes_nonempty l12mg_w5381_not_written.2
  rw [e2]
  exact hPM 5381 [1024,512] (by native_decide)

/-! ### Goals -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5380_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5380)
      (denoteGraphDistributedFaithful pm initPM 9795)
      (denoteGraphDistributedFaithful pm initPM 9796)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5379_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12mg_red_sm5380 initSM, l12mg_red_pm9795 initPM, l12mg_red_pm9796 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5382_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5382)
      (denoteGraphDistributedFaithful pm initPM 9801)
      (denoteGraphDistributedFaithful pm initPM 9802)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5380_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq := l12mg_w5381_eq initSM initPM hInit
  have hwShape := l12mg_w5381_shape initPM hPM
  rw [l12mg_red_sm5382 initSM, l12mg_red_pm9801 initPM, l12mg_red_pm9802 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5383_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5383)
      (denoteGraphDistributedFaithful pm initPM 9811)
      (denoteGraphDistributedFaithful pm initPM 9812)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5382_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12mg_red_sm5383 initSM, l12mg_red_pm9811 initPM, l12mg_red_pm9812 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5384_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5384)
      (denoteGraphDistributedFaithful pm initPM 9815)
      (denoteGraphDistributedFaithful pm initPM 9816)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5370_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5383_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5370)
      (denoteGraphDistributedFaithful pm initPM 9755)
      (denoteGraphDistributedFaithful pm initPM 9756)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 1] [2048, 1] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5383)
      (denoteGraphDistributedFaithful pm initPM 9811)
      (denoteGraphDistributedFaithful pm initPM 9812)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l12mg_red_sm5384 initSM, l12mg_red_pm9815 initPM, l12mg_red_pm9816 initPM]
  exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hA' hB' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
