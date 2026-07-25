/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L13FaithfulZigzagAttention
import denote.yoco_goals.L12FaithfulRouterEntry

/-!
# Faithful zigzag relations for the block-1 entry segment

Continuation of `recon_zigzagGoal_5396_faithful` (block-1 cross-decoder
attention) through the block-1 entry segment:

* SM 541: `FW_reshape [5396] → [5397]`   (PM 1144/1145: `9859 → 9861`, `9860 → 9862`)
* SM 542: `FW_reshape [5397] → [5398]`   (PM 1146/1147: `9861 → 9867`, `9862 → 9868`)
* SM 543: `FW_mix_precision_linear [5398, 5399] → [5400]`
                                          (PM 1148/1149 with replicated weight 5399)
* SM 544: `FW_view [5400] → [5401]`      (PM 1150/1151)
* SM 545: `FW_float [5401] → [5402]`     (PM 1152/1153)
* SM 546: `FW_add [8182, 5402] → [5403]` (PM 1154/1155 with bypass 16051/16059)
* SM 547: `FW_multiref [5403] → [8186, 8190]`
                                          (PM 1156: `[16063, 16067]`, PM 1157: `[16071, 16075]`)
* SM 548: `FW_rms_norm [8186, 5404] → [5405]` (PM 1158/1159, replicated weight 5404)
* SM 549: `FW_multiref [5405] → [8197, 8201, 8205, 8209, 8213]`
                                          (PM 1160: `[16082, 16086, 16090, 16094, 16098]`,
                                           PM 1161: `[16105, 16109, 16113, 16117, 16121]`)

All relations are stated against the block-1 cumulative-sequence metadata tensor
`5394` (the same cu slot used by `recon_zigzagGoal_5396_faithful`).
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

/-! ### Local `applyNode` helper for the first output of a 5-way multiref -/

private theorem l13en_multiref5_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 t4 t5 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := [t1, t2, t3, t4, t5], params := [5] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3, t4, t5].zip (List.replicate 5 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ### Node literals -/

private def l13enSmReshape5397 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5396], outs := [5397],
    params := [4096, 1024] }
private def l13enSmReshape5398 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5397], outs := [5398],
    params := [4096, 1024] }
private def l13enSmLinear5400 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5398, 5399],
    outs := [5400] }
private def l13enSmView5401 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5400], outs := [5401],
    params := [4096, 1024] }
private def l13enSmFloat5402 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5401], outs := [5402] }
private def l13enSmAdd5403 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8182, 5402], outs := [5403] }
private def l13enSmMulti2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5403], outs := [8186, 8190],
    params := [2] }
private def l13enSmRms5405 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8186, 5404], outs := [5405] }
private def l13enSmMulti5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5405],
    outs := [8197, 8201, 8205, 8209, 8213], params := [5] }

private def l13enPmReshape9861 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9859], outs := [9861],
    params := [2048, 1024] }
private def l13enPmReshape9862 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9860], outs := [9862],
    params := [2048, 1024] }
private def l13enPmReshape9867 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9861], outs := [9867],
    params := [2048, 1024] }
private def l13enPmReshape9868 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9862], outs := [9868],
    params := [2048, 1024] }
private def l13enPmLinear9871 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9867, 5399],
    outs := [9871] }
private def l13enPmLinear9872 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9868, 5399],
    outs := [9872] }
private def l13enPmView9881 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9871], outs := [9881],
    params := [2048, 1024] }
private def l13enPmView9882 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9872], outs := [9882],
    params := [2048, 1024] }
private def l13enPmFloat9885 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9881], outs := [9885] }
private def l13enPmFloat9886 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9882], outs := [9886] }
private def l13enPmAdd9889 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16051, 9885], outs := [9889] }
private def l13enPmAdd9890 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16059, 9886], outs := [9890] }
private def l13enPmMulti2R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9889], outs := [16063, 16067],
    params := [2] }
private def l13enPmMulti2R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9890], outs := [16071, 16075],
    params := [2] }
private def l13enPmRms9893 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16063, 5404], outs := [9893] }
private def l13enPmRms9894 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16071, 5404], outs := [9894] }
private def l13enPmMulti5R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9893],
    outs := [16082, 16086, 16090, 16094, 16098], params := [5] }
private def l13enPmMulti5R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9894],
    outs := [16105, 16109, 16113, 16117, 16121], params := [5] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l13en_sm_node_facts :
    sm.nodes[541]'(by native_decide) = l13enSmReshape5397 ∧
    sm.nodes[542]'(by native_decide) = l13enSmReshape5398 ∧
    sm.nodes[543]'(by native_decide) = l13enSmLinear5400 ∧
    sm.nodes[544]'(by native_decide) = l13enSmView5401 ∧
    sm.nodes[545]'(by native_decide) = l13enSmFloat5402 ∧
    sm.nodes[546]'(by native_decide) = l13enSmAdd5403 ∧
    sm.nodes[547]'(by native_decide) = l13enSmMulti2 ∧
    sm.nodes[548]'(by native_decide) = l13enSmRms5405 ∧
    sm.nodes[549]'(by native_decide) = l13enSmMulti5 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l13en_pm_node_facts :
    pm.nodes[1144]'(by native_decide) = l13enPmReshape9861 ∧
    pm.nodes[1145]'(by native_decide) = l13enPmReshape9862 ∧
    pm.nodes[1146]'(by native_decide) = l13enPmReshape9867 ∧
    pm.nodes[1147]'(by native_decide) = l13enPmReshape9868 ∧
    pm.nodes[1148]'(by native_decide) = l13enPmLinear9871 ∧
    pm.nodes[1149]'(by native_decide) = l13enPmLinear9872 ∧
    pm.nodes[1150]'(by native_decide) = l13enPmView9881 ∧
    pm.nodes[1151]'(by native_decide) = l13enPmView9882 ∧
    pm.nodes[1152]'(by native_decide) = l13enPmFloat9885 ∧
    pm.nodes[1153]'(by native_decide) = l13enPmFloat9886 ∧
    pm.nodes[1154]'(by native_decide) = l13enPmAdd9889 ∧
    pm.nodes[1155]'(by native_decide) = l13enPmAdd9890 ∧
    pm.nodes[1156]'(by native_decide) = l13enPmMulti2R0 ∧
    pm.nodes[1157]'(by native_decide) = l13enPmMulti2R1 ∧
    pm.nodes[1158]'(by native_decide) = l13enPmRms9893 ∧
    pm.nodes[1159]'(by native_decide) = l13enPmRms9894 ∧
    pm.nodes[1160]'(by native_decide) = l13enPmMulti5R0 ∧
    pm.nodes[1161]'(by native_decide) = l13enPmMulti5R1 := by
  native_decide

private theorem l13en_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l13en_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l13en_weights_not_written :
    (∀ n ∈ sm.nodes, 5399 ∉ n.outs ∧ 5404 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5399 ∉ n.outs ∧ 5404 ∉ n.outs) := by
  native_decide

private theorem l13en_w5399_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5399 ∉ n.outs := by
  intro n hn
  exact (l13en_weights_not_written.1 n (List.mem_of_mem_drop hn)).1

private theorem l13en_w5399_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5399 ∉ n.outs := by
  intro n hn
  exact (l13en_weights_not_written.2 n (List.mem_of_mem_drop hn)).1

private theorem l13en_w5404_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5404 ∉ n.outs := by
  intro n hn
  exact (l13en_weights_not_written.1 n (List.mem_of_mem_drop hn)).2

private theorem l13en_w5404_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5404 ∉ n.outs := by
  intro n hn
  exact (l13en_weights_not_written.2 n (List.mem_of_mem_drop hn)).2

set_option maxRecDepth 1000000 in
private theorem l13en_cu_not_written :
    ∀ n ∈ pm.nodes, 5345 ∉ n.outs ∧ 5394 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l13en_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(542, 5397), (541, 5396), (543, 5398), (544, 5400), (545, 5401), (546,
      5402), (547, 5403), (546, 8182), (548, 8186), (548, 8190), (549, 5405),
      (550, 8197), (550, 8201), (550, 8205), (550, 8209), (550, 8213)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l13en_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1145, 9861), (1144, 9859), (1146, 9862), (1145, 9860), (1147, 9867),
      (1146, 9861), (1148, 9868), (1147, 9862), (1149, 9871), (1148, 9867),
      (1150, 9872), (1149, 9868), (1151, 9881), (1150, 9871), (1152, 9882),
      (1151, 9872), (1153, 9885), (1152, 9881), (1154, 9886), (1153, 9882),
      (1155, 9889), (1154, 16051), (1154, 9885), (1156, 9890), (1155, 16059),
      (1155, 9886), (1157, 16063), (1157, 16067), (1156, 9889), (1158, 16071),
      (1158, 16075), (1157, 9890), (1159, 9893), (1158, 16063), (1160, 9894),
      (1159, 16071), (1161, 16082), (1161, 16086), (1161, 16090), (1161, 16094),
      (1161, 16098), (1160, 9893), (1162, 16105), (1162, 16109), (1162, 16113),
      (1162, 16117), (1162, 16121), (1161, 9894)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm5397 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5397 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5396) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 541 l13enSmReshape5397
    5396 5397 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l13en_sm_node_facts.1 ?_
    (l13en_nonempty_sm 542) (l13en_sm_not_written 542 5397 (by decide))
    (l13en_nonempty_sm 541) (l13en_sm_not_written 541 5396 (by decide))
  intro s
  unfold l13enSmReshape5397
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5396 5397 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9861 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9861 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9859) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1144 l13enPmReshape9861
    9859 9861 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l13en_pm_node_facts.1 ?_
    (l13en_nonempty_pm 1145) (l13en_pm_not_written 1145 9861 (by decide))
    (l13en_nonempty_pm 1144) (l13en_pm_not_written 1144 9859 (by decide))
  intro s
  unfold l13enPmReshape9861
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 9859 9861 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9862 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9862 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9860) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1145 l13enPmReshape9862
    9860 9862 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l13en_pm_node_facts.2.1 ?_
    (l13en_nonempty_pm 1146) (l13en_pm_not_written 1146 9862 (by decide))
    (l13en_nonempty_pm 1145) (l13en_pm_not_written 1145 9860 (by decide))
  intro s
  unfold l13enPmReshape9862
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 9860 9862 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm5398 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5398 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5397) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 542 l13enSmReshape5398
    5397 5398 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l13en_sm_node_facts.2.1 ?_
    (l13en_nonempty_sm 543) (l13en_sm_not_written 543 5398 (by decide))
    (l13en_nonempty_sm 542) (l13en_sm_not_written 542 5397 (by decide))
  intro s
  unfold l13enSmReshape5398
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5397 5398 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9867 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9867 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9861) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1146 l13enPmReshape9867
    9861 9867 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l13en_pm_node_facts.2.2.1 ?_
    (l13en_nonempty_pm 1147) (l13en_pm_not_written 1147 9867 (by decide))
    (l13en_nonempty_pm 1146) (l13en_pm_not_written 1146 9861 (by decide))
  intro s
  unfold l13enPmReshape9867
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 9861 9867 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9868 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9868 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9862) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1147 l13enPmReshape9868
    9862 9868 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l13en_pm_node_facts.2.2.2.1 ?_
    (l13en_nonempty_pm 1148) (l13en_pm_not_written 1148 9868 (by decide))
    (l13en_nonempty_pm 1147) (l13en_pm_not_written 1147 9862 (by decide))
  intro s
  unfold l13enPmReshape9868
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 9862 9868 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm5400 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5400 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5398)
        (denoteGraphDistributedFaithful sm initSM 5399) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 543 l13enSmLinear5400
    5398 5399 5400 fw_linear
    (by native_decide) l13en_sm_node_facts.2.2.1 ?_
    (l13en_nonempty_sm 544) (l13en_sm_not_written 544 5400 (by decide))
    (l13en_nonempty_sm 543) (l13en_sm_not_written 543 5398 (by decide))
    (l13en_w5399_sm_drop 543)
  intro s
  unfold l13enSmLinear5400
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5398 5399 5400

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9871 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9871 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9867)
        (denoteGraphDistributedFaithful pm initPM 5399) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1148 l13enPmLinear9871
    9867 5399 9871 fw_linear
    (by native_decide) l13en_pm_node_facts.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1149) (l13en_pm_not_written 1149 9871 (by decide))
    (l13en_nonempty_pm 1148) (l13en_pm_not_written 1148 9867 (by decide))
    (l13en_w5399_pm_drop 1148)
  intro s
  unfold l13enPmLinear9871
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 9867 5399 9871

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9872 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9872 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9868)
        (denoteGraphDistributedFaithful pm initPM 5399) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1149 l13enPmLinear9872
    9868 5399 9872 fw_linear
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1150) (l13en_pm_not_written 1150 9872 (by decide))
    (l13en_nonempty_pm 1149) (l13en_pm_not_written 1149 9868 (by decide))
    (l13en_w5399_pm_drop 1149)
  intro s
  unfold l13enPmLinear9872
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 9868 5399 9872

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm5401 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5401 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5400) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 544 l13enSmView5401
    5400 5401 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l13en_sm_node_facts.2.2.2.1 ?_
    (l13en_nonempty_sm 545) (l13en_sm_not_written 545 5401 (by decide))
    (l13en_nonempty_sm 544) (l13en_sm_not_written 544 5400 (by decide))
  intro s
  unfold l13enSmView5401
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5400 5401

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9881 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9881 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9871) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1150 l13enPmView9881
    9871 9881 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1151) (l13en_pm_not_written 1151 9881 (by decide))
    (l13en_nonempty_pm 1150) (l13en_pm_not_written 1150 9871 (by decide))
  intro s
  unfold l13enPmView9881
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 9871 9881

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9882 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9882 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9872) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1151 l13enPmView9882
    9872 9882 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1152) (l13en_pm_not_written 1152 9882 (by decide))
    (l13en_nonempty_pm 1151) (l13en_pm_not_written 1151 9872 (by decide))
  intro s
  unfold l13enPmView9882
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 9872 9882

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm5402 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5402 =
      denoteGraphDistributedFaithful sm initSM 5401 := by
  have h := denoteGraphDistributedFaithful_reduce1 sm initSM 545 l13enSmFloat5402
    5401 5402 id
    (by native_decide) l13en_sm_node_facts.2.2.2.2.1 ?_
    (l13en_nonempty_sm 546) (l13en_sm_not_written 546 5402 (by decide))
    (l13en_nonempty_sm 545) (l13en_sm_not_written 545 5401 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l13enSmFloat5402
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out sm s 0 5401 5402 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9885 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9885 =
      denoteGraphDistributedFaithful pm initPM 9881 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1152 l13enPmFloat9885
    9881 9885 id
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1153) (l13en_pm_not_written 1153 9885 (by decide))
    (l13en_nonempty_pm 1152) (l13en_pm_not_written 1152 9881 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l13enPmFloat9885
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 0 9881 9885 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9886 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9886 =
      denoteGraphDistributedFaithful pm initPM 9882 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1153 l13enPmFloat9886
    9882 9886 id
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1154) (l13en_pm_not_written 1154 9886 (by decide))
    (l13en_nonempty_pm 1153) (l13en_pm_not_written 1153 9882 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l13enPmFloat9886
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 1 9882 9886 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm5403 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5403 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8182)
        (denoteGraphDistributedFaithful sm initSM 5402) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 546 l13enSmAdd5403
    8182 5402 5403 elemwiseAdd
    (by native_decide) l13en_sm_node_facts.2.2.2.2.2.1 ?_
    (l13en_nonempty_sm 547) (l13en_sm_not_written 547 5403 (by decide))
    (l13en_nonempty_sm 546) (l13en_sm_not_written 546 8182 (by decide))
    (l13en_sm_not_written 546 5402 (by decide))
  intro s
  unfold l13enSmAdd5403
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8182 5402 5403

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9889 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9889 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16051)
        (denoteGraphDistributedFaithful pm initPM 9885) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1154 l13enPmAdd9889
    16051 9885 9889 elemwiseAdd
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1155) (l13en_pm_not_written 1155 9889 (by decide))
    (l13en_nonempty_pm 1154) (l13en_pm_not_written 1154 16051 (by decide))
    (l13en_pm_not_written 1154 9885 (by decide))
  intro s
  unfold l13enPmAdd9889
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16051 9885 9889

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9890 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9890 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16059)
        (denoteGraphDistributedFaithful pm initPM 9886) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1155 l13enPmAdd9890
    16059 9886 9890 elemwiseAdd
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1156) (l13en_pm_not_written 1156 9890 (by decide))
    (l13en_nonempty_pm 1155) (l13en_pm_not_written 1155 16059 (by decide))
    (l13en_pm_not_written 1155 9886 (by decide))
  intro s
  unfold l13enPmAdd9890
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16059 9886 9890

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm8186 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8186 =
      denoteGraphDistributedFaithful sm initSM 5403 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 547 l13enSmMulti2
    5403 8186 (fun x => x)
    (by native_decide) l13en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_sm 548) (l13en_sm_not_written 548 8186 (by decide))
    (l13en_nonempty_sm 547) (l13en_sm_not_written 547 5403 (by decide))
  intro s
  unfold l13enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5403 8186 8190

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm8190 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8190 =
      denoteGraphDistributedFaithful sm initSM 5403 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 547 l13enSmMulti2
    5403 8190 (fun x => x)
    (by native_decide) l13en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_sm 548) (l13en_sm_not_written 548 8190 (by decide))
    (l13en_nonempty_sm 547) (l13en_sm_not_written 547 5403 (by decide))
  intro s
  unfold l13enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5403 8186 8190 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16063 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16063 =
      denoteGraphDistributedFaithful pm initPM 9889 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1156 l13enPmMulti2R0
    9889 16063 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1157) (l13en_pm_not_written 1157 16063 (by decide))
    (l13en_nonempty_pm 1156) (l13en_pm_not_written 1156 9889 (by decide))
  intro s
  unfold l13enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 9889 16063 16067

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16067 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16067 =
      denoteGraphDistributedFaithful pm initPM 9889 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1156 l13enPmMulti2R0
    9889 16067 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1157) (l13en_pm_not_written 1157 16067 (by decide))
    (l13en_nonempty_pm 1156) (l13en_pm_not_written 1156 9889 (by decide))
  intro s
  unfold l13enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 9889 16063 16067 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16071 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16071 =
      denoteGraphDistributedFaithful pm initPM 9890 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1157 l13enPmMulti2R1
    9890 16071 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1158) (l13en_pm_not_written 1158 16071 (by decide))
    (l13en_nonempty_pm 1157) (l13en_pm_not_written 1157 9890 (by decide))
  intro s
  unfold l13enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 9890 16071 16075

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16075 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16075 =
      denoteGraphDistributedFaithful pm initPM 9890 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1157 l13enPmMulti2R1
    9890 16075 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1158) (l13en_pm_not_written 1158 16075 (by decide))
    (l13en_nonempty_pm 1157) (l13en_pm_not_written 1157 9890 (by decide))
  intro s
  unfold l13enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 9890 16071 16075 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm5405 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5405 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8186)
        (denoteGraphDistributedFaithful sm initSM 5404) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 548 l13enSmRms5405
    8186 5404 5405 fw_rms_norm
    (by native_decide) l13en_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_sm 549) (l13en_sm_not_written 549 5405 (by decide))
    (l13en_nonempty_sm 548) (l13en_sm_not_written 548 8186 (by decide))
    (l13en_w5404_sm_drop 548)
  intro s
  unfold l13enSmRms5405
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8186 5404 5405

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9893 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9893 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16063)
        (denoteGraphDistributedFaithful pm initPM 5404) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1158 l13enPmRms9893
    16063 5404 9893 fw_rms_norm
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1159) (l13en_pm_not_written 1159 9893 (by decide))
    (l13en_nonempty_pm 1158) (l13en_pm_not_written 1158 16063 (by decide))
    (l13en_w5404_pm_drop 1158)
  intro s
  unfold l13enPmRms9893
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16063 5404 9893

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm9894 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9894 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16071)
        (denoteGraphDistributedFaithful pm initPM 5404) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1159 l13enPmRms9894
    16071 5404 9894 fw_rms_norm
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1160) (l13en_pm_not_written 1160 9894 (by decide))
    (l13en_nonempty_pm 1159) (l13en_pm_not_written 1159 16071 (by decide))
    (l13en_w5404_pm_drop 1159)
  intro s
  unfold l13enPmRms9894
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16071 5404 9894

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm8197 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8197 =
      denoteGraphDistributedFaithful sm initSM 5405 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 549 l13enSmMulti5
    5405 8197 (fun x => x)
    (by native_decide) l13en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l13en_nonempty_sm 550) (l13en_sm_not_written 550 8197 (by decide))
    (l13en_nonempty_sm 549) (l13en_sm_not_written 549 5405 (by decide))
  intro s
  unfold l13enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l13en_multiref5_first_out sm s 0 5405 8197 8201 8205 8209 8213

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm8201 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8201 =
      denoteGraphDistributedFaithful sm initSM 5405 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 549 l13enSmMulti5
    5405 8201 (fun x => x)
    (by native_decide) l13en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l13en_nonempty_sm 550) (l13en_sm_not_written 550 8201 (by decide))
    (l13en_nonempty_sm 549) (l13en_sm_not_written 549 5405 (by decide))
  intro s
  unfold l13enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out sm s 0 5405 8197 8201 8205 8209 8213
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm8205 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8205 =
      denoteGraphDistributedFaithful sm initSM 5405 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 549 l13enSmMulti5
    5405 8205 (fun x => x)
    (by native_decide) l13en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l13en_nonempty_sm 550) (l13en_sm_not_written 550 8205 (by decide))
    (l13en_nonempty_sm 549) (l13en_sm_not_written 549 5405 (by decide))
  intro s
  unfold l13enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out sm s 0 5405 8197 8201 8205 8209 8213
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm8209 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8209 =
      denoteGraphDistributedFaithful sm initSM 5405 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 549 l13enSmMulti5
    5405 8209 (fun x => x)
    (by native_decide) l13en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l13en_nonempty_sm 550) (l13en_sm_not_written 550 8209 (by decide))
    (l13en_nonempty_sm 549) (l13en_sm_not_written 549 5405 (by decide))
  intro s
  unfold l13enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out sm s 0 5405 8197 8201 8205 8209 8213
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_sm8213 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8213 =
      denoteGraphDistributedFaithful sm initSM 5405 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 549 l13enSmMulti5
    5405 8213 (fun x => x)
    (by native_decide) l13en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l13en_nonempty_sm 550) (l13en_sm_not_written 550 8213 (by decide))
    (l13en_nonempty_sm 549) (l13en_sm_not_written 549 5405 (by decide))
  intro s
  unfold l13enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out sm s 0 5405 8197 8201 8205 8209 8213
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16082 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16082 =
      denoteGraphDistributedFaithful pm initPM 9893 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1160 l13enPmMulti5R0
    9893 16082 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1161) (l13en_pm_not_written 1161 16082 (by decide))
    (l13en_nonempty_pm 1160) (l13en_pm_not_written 1160 9893 (by decide))
  intro s
  unfold l13enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l13en_multiref5_first_out pm s 0 9893 16082 16086 16090 16094 16098

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16086 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16086 =
      denoteGraphDistributedFaithful pm initPM 9893 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1160 l13enPmMulti5R0
    9893 16086 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1161) (l13en_pm_not_written 1161 16086 (by decide))
    (l13en_nonempty_pm 1160) (l13en_pm_not_written 1160 9893 (by decide))
  intro s
  unfold l13enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 0 9893 16082 16086 16090 16094 16098
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16090 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16090 =
      denoteGraphDistributedFaithful pm initPM 9893 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1160 l13enPmMulti5R0
    9893 16090 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1161) (l13en_pm_not_written 1161 16090 (by decide))
    (l13en_nonempty_pm 1160) (l13en_pm_not_written 1160 9893 (by decide))
  intro s
  unfold l13enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 0 9893 16082 16086 16090 16094 16098
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16094 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16094 =
      denoteGraphDistributedFaithful pm initPM 9893 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1160 l13enPmMulti5R0
    9893 16094 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1161) (l13en_pm_not_written 1161 16094 (by decide))
    (l13en_nonempty_pm 1160) (l13en_pm_not_written 1160 9893 (by decide))
  intro s
  unfold l13enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 0 9893 16082 16086 16090 16094 16098
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16098 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16098 =
      denoteGraphDistributedFaithful pm initPM 9893 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1160 l13enPmMulti5R0
    9893 16098 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13en_nonempty_pm 1161) (l13en_pm_not_written 1161 16098 (by decide))
    (l13en_nonempty_pm 1160) (l13en_pm_not_written 1160 9893 (by decide))
  intro s
  unfold l13enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 0 9893 16082 16086 16090 16094 16098
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16105 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16105 =
      denoteGraphDistributedFaithful pm initPM 9894 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1161 l13enPmMulti5R1
    9894 16105 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l13en_nonempty_pm 1162) (l13en_pm_not_written 1162 16105 (by decide))
    (l13en_nonempty_pm 1161) (l13en_pm_not_written 1161 9894 (by decide))
  intro s
  unfold l13enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l13en_multiref5_first_out pm s 1 9894 16105 16109 16113 16117 16121

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16109 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16109 =
      denoteGraphDistributedFaithful pm initPM 9894 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1161 l13enPmMulti5R1
    9894 16109 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l13en_nonempty_pm 1162) (l13en_pm_not_written 1162 16109 (by decide))
    (l13en_nonempty_pm 1161) (l13en_pm_not_written 1161 9894 (by decide))
  intro s
  unfold l13enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 1 9894 16105 16109 16113 16117 16121
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16113 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16113 =
      denoteGraphDistributedFaithful pm initPM 9894 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1161 l13enPmMulti5R1
    9894 16113 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l13en_nonempty_pm 1162) (l13en_pm_not_written 1162 16113 (by decide))
    (l13en_nonempty_pm 1161) (l13en_pm_not_written 1161 9894 (by decide))
  intro s
  unfold l13enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 1 9894 16105 16109 16113 16117 16121
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16117 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16117 =
      denoteGraphDistributedFaithful pm initPM 9894 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1161 l13enPmMulti5R1
    9894 16117 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l13en_nonempty_pm 1162) (l13en_pm_not_written 1162 16117 (by decide))
    (l13en_nonempty_pm 1161) (l13en_pm_not_written 1161 9894 (by decide))
  intro s
  unfold l13enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 1 9894 16105 16109 16113 16117 16121
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13en_red_pm16121 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16121 =
      denoteGraphDistributedFaithful pm initPM 9894 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1161 l13enPmMulti5R1
    9894 16121 (fun x => x)
    (by native_decide) l13en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l13en_nonempty_pm 1162) (l13en_pm_not_written 1162 16121 (by decide))
    (l13en_nonempty_pm 1161) (l13en_pm_not_written 1161 9894 (by decide))
  intro s
  unfold l13enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 1 9894 16105 16109 16113 16117 16121
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5397 (`FW_reshape` of 5396).
theorem recon_zigzagGoal_5397_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5397)
      (denoteGraphDistributedFaithful pm initPM 9861)
      (denoteGraphDistributedFaithful pm initPM 9862)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5396_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13en_red_sm5397 initSM, l13en_red_pm9861 initPM, l13en_red_pm9862 initPM]
  exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hparent (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5398 (`FW_reshape` of 5397).
theorem recon_zigzagGoal_5398_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5398)
      (denoteGraphDistributedFaithful pm initPM 9867)
      (denoteGraphDistributedFaithful pm initPM 9868)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5397_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13en_red_sm5398 initSM, l13en_red_pm9867 initPM, l13en_red_pm9868 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5400 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5400_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5400)
      (denoteGraphDistributedFaithful pm initPM 9871)
      (denoteGraphDistributedFaithful pm initPM 9872)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5398_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5399 = initPM 5399 :=
    recon_weight initSM initPM hInit initGoal_5399 (by native_decide) 5399
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5399 = initSM 5399 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5399
      layer1_sm_nodes_nonempty (fun n hn => (l13en_weights_not_written.1 n hn).1)
  have hpw : denoteGraphDistributedFaithful pm initPM 5399 = initPM 5399 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5399
      layer1_pm_nodes_nonempty (fun n hn => (l13en_weights_not_written.2 n hn).1)
  have hw : denoteGraphDistributedFaithful sm initSM 5399 =
      denoteGraphDistributedFaithful pm initPM 5399 := by
    rw [hsw, hpw]; exact hwInit
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5399).shape =
      [1024, 1024] := by
    rw [hpw]
    exact hPM 5399 [1024, 1024] (by native_decide)
  rw [l13en_red_sm5400 initSM, l13en_red_pm9871 initPM, l13en_red_pm9872 initPM, hw]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5401 (`FW_view` of 5400).
theorem recon_zigzagGoal_5401_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5401)
      (denoteGraphDistributedFaithful pm initPM 9881)
      (denoteGraphDistributedFaithful pm initPM 9882)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5400_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13en_red_sm5401 initSM, l13en_red_pm9881 initPM, l13en_red_pm9882 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5402 (`FW_float` of 5401).
theorem recon_zigzagGoal_5402_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5402)
      (denoteGraphDistributedFaithful pm initPM 9885)
      (denoteGraphDistributedFaithful pm initPM 9886)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5401_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13en_red_sm5402 initSM, l13en_red_pm9885 initPM, l13en_red_pm9886 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5403 (residual `FW_add` of the
-- cross-layer bypass 8182 and 5402).
theorem recon_zigzagGoal_5403_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5403)
      (denoteGraphDistributedFaithful pm initPM 9889)
      (denoteGraphDistributedFaithful pm initPM 9890)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8182_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5402_faithful initSM initPM hSM hPM hInit hValues hCu
  have pmFinal (tid : Tid) (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hw
  have h5345_5394 : denoteGraphDistributedFaithful pm initPM 5345 =
      denoteGraphDistributedFaithful pm initPM 5394 := by
    rw [pmFinal 5345 (fun n hn => (l13en_cu_not_written n hn).1),
      pmFinal 5394 (fun n hn => (l13en_cu_not_written n hn).2)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  rw [h5345_5394] at hA
  rw [l13en_red_sm5403 initSM, l13en_red_pm9889 initPM, l13en_red_pm9890 initPM]
  exact Zigzag2Rel.add 2048 1024 hA hB (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8186 (2-way multiref, position 0).
theorem recon_zigzagGoal_8186_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8186)
      (denoteGraphDistributedFaithful pm initPM 16063)
      (denoteGraphDistributedFaithful pm initPM 16071)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5403_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13en_red_sm8186 initSM, l13en_red_pm16063 initPM, l13en_red_pm16071 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8190 (2-way multiref, position 1).
theorem recon_zigzagGoal_8190_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8190)
      (denoteGraphDistributedFaithful pm initPM 16067)
      (denoteGraphDistributedFaithful pm initPM 16075)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5403_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13en_red_sm8190 initSM, l13en_red_pm16067 initPM, l13en_red_pm16075 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5405 (`FW_rms_norm` of 8186 with
-- the replicated weight 5404).
theorem recon_zigzagGoal_5405_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5405)
      (denoteGraphDistributedFaithful pm initPM 9893)
      (denoteGraphDistributedFaithful pm initPM 9894)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8186_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5404 = initPM 5404 :=
    recon_weight initSM initPM hInit initGoal_5404 (by native_decide) 5404
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5404 = initSM 5404 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5404
      layer1_sm_nodes_nonempty (fun n hn => (l13en_weights_not_written.1 n hn).2)
  have hpw : denoteGraphDistributedFaithful pm initPM 5404 = initPM 5404 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5404
      layer1_pm_nodes_nonempty (fun n hn => (l13en_weights_not_written.2 n hn).2)
  have hw : denoteGraphDistributedFaithful sm initSM 5404 =
      denoteGraphDistributedFaithful pm initPM 5404 := by
    rw [hsw, hpw]; exact hwInit
  rw [l13en_red_sm5405 initSM, l13en_red_pm9893 initPM, l13en_red_pm9894 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8197 (5-way multiref, position 0).
theorem recon_zigzagGoal_8197_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8197)
      (denoteGraphDistributedFaithful pm initPM 16082)
      (denoteGraphDistributedFaithful pm initPM 16105)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5405_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13en_red_sm8197 initSM, l13en_red_pm16082 initPM, l13en_red_pm16105 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8201 (5-way multiref, position 1).
theorem recon_zigzagGoal_8201_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8201)
      (denoteGraphDistributedFaithful pm initPM 16086)
      (denoteGraphDistributedFaithful pm initPM 16109)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5405_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13en_red_sm8201 initSM, l13en_red_pm16086 initPM, l13en_red_pm16109 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8205 (5-way multiref, position 2).
theorem recon_zigzagGoal_8205_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8205)
      (denoteGraphDistributedFaithful pm initPM 16090)
      (denoteGraphDistributedFaithful pm initPM 16113)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5405_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13en_red_sm8205 initSM, l13en_red_pm16090 initPM, l13en_red_pm16113 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8209 (5-way multiref, position 3).
theorem recon_zigzagGoal_8209_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8209)
      (denoteGraphDistributedFaithful pm initPM 16094)
      (denoteGraphDistributedFaithful pm initPM 16117)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5405_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13en_red_sm8209 initSM, l13en_red_pm16094 initPM, l13en_red_pm16117 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8213 (5-way multiref, position 4).
theorem recon_zigzagGoal_8213_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8213)
      (denoteGraphDistributedFaithful pm initPM 16098)
      (denoteGraphDistributedFaithful pm initPM 16121)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5405_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13en_red_sm8213 initSM, l13en_red_pm16098 initPM, l13en_red_pm16121 initPM]
  exact hparent

end
end TrainVerify.Denote.GeneratedPatterns
