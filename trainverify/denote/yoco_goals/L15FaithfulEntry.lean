/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L15FaithfulZigzagAttention
import denote.yoco_goals.L14FaithfulBlockTail
import denote.yoco_goals.L12FaithfulRouterEntry

/-!
# Faithful zigzag relations for the block-3 entry segment

Continuation of `recon_zigzagGoal_5494_faithful` (block-3 cross-decoder
attention) through the block-3 entry segment:

* SM 611: `FW_reshape [5494] → [5495]`   (PM 1284/1285: `10203 → 10205`, `10204 → 10206`)
* SM 612: `FW_reshape [5495] → [5496]`   (PM 1286/1287: `10205 → 10211`, `10206 → 10212`)
* SM 613: `FW_mix_precision_linear [5496, 5497] → [5498]`
                                          (PM 1288/1289 with replicated weight 5497)
* SM 614: `FW_view [5498] → [5499]`      (PM 1290/1291)
* SM 615: `FW_float [5499] → [5500]`     (PM 1292/1293)
* SM 616: `FW_add [8260, 5500] → [5501]` (PM 1294/1295 with bypass 16207/16215)
* SM 617: `FW_multiref [5501] → [8264, 8268]`
                                          (PM 1296: `[16219, 16223]`, PM 1297: `[16227, 16231]`)
* SM 618: `FW_rms_norm [8264, 5502] → [5503]` (PM 1298/1299, replicated weight 5502)
* SM 619: `FW_multiref [5503] → [8275, 8279, 8283, 8287, 8291]`
                                          (PM 1300: `[16238, 16242, 16246, 16250, 16254]`,
                                           PM 1301: `[16261, 16265, 16269, 16273, 16277]`)

All relations are stated against the block-3 cumulative-sequence metadata tensor
`5492` (the same cu slot used by `recon_zigzagGoal_5494_faithful`).
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

private theorem l15en_multiref5_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 t4 t5 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := [t1, t2, t3, t4, t5], params := [5] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3, t4, t5].zip (List.replicate 5 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ### Node literals -/

private def l15enSmReshape5495 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5494], outs := [5495],
    params := [4096, 1024] }
private def l15enSmReshape5496 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5495], outs := [5496],
    params := [4096, 1024] }
private def l15enSmLinear5498 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5496, 5497],
    outs := [5498] }
private def l15enSmView5499 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5498], outs := [5499],
    params := [4096, 1024] }
private def l15enSmFloat5500 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5499], outs := [5500] }
private def l15enSmAdd5501 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8260, 5500], outs := [5501] }
private def l15enSmMulti2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5501], outs := [8264, 8268],
    params := [2] }
private def l15enSmRms5503 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8264, 5502], outs := [5503] }
private def l15enSmMulti5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5503],
    outs := [8275, 8279, 8283, 8287, 8291], params := [5] }

private def l15enPmReshape10205 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10203], outs := [10205],
    params := [2048, 1024] }
private def l15enPmReshape10206 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10204], outs := [10206],
    params := [2048, 1024] }
private def l15enPmReshape10211 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10205], outs := [10211],
    params := [2048, 1024] }
private def l15enPmReshape10212 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10206], outs := [10212],
    params := [2048, 1024] }
private def l15enPmLinear10215 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10211, 5497],
    outs := [10215] }
private def l15enPmLinear10216 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10212, 5497],
    outs := [10216] }
private def l15enPmView10225 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10215], outs := [10225],
    params := [2048, 1024] }
private def l15enPmView10226 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10216], outs := [10226],
    params := [2048, 1024] }
private def l15enPmFloat10229 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10225], outs := [10229] }
private def l15enPmFloat10230 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10226], outs := [10230] }
private def l15enPmAdd10233 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16207, 10229], outs := [10233] }
private def l15enPmAdd10234 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16215, 10230], outs := [10234] }
private def l15enPmMulti2R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10233], outs := [16219, 16223],
    params := [2] }
private def l15enPmMulti2R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10234], outs := [16227, 16231],
    params := [2] }
private def l15enPmRms10237 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16219, 5502], outs := [10237] }
private def l15enPmRms10238 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16227, 5502], outs := [10238] }
private def l15enPmMulti5R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10237],
    outs := [16238, 16242, 16246, 16250, 16254], params := [5] }
private def l15enPmMulti5R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10238],
    outs := [16261, 16265, 16269, 16273, 16277], params := [5] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l15en_sm_node_facts :
    sm.nodes[611]'(by native_decide) = l15enSmReshape5495 ∧
    sm.nodes[612]'(by native_decide) = l15enSmReshape5496 ∧
    sm.nodes[613]'(by native_decide) = l15enSmLinear5498 ∧
    sm.nodes[614]'(by native_decide) = l15enSmView5499 ∧
    sm.nodes[615]'(by native_decide) = l15enSmFloat5500 ∧
    sm.nodes[616]'(by native_decide) = l15enSmAdd5501 ∧
    sm.nodes[617]'(by native_decide) = l15enSmMulti2 ∧
    sm.nodes[618]'(by native_decide) = l15enSmRms5503 ∧
    sm.nodes[619]'(by native_decide) = l15enSmMulti5 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l15en_pm_node_facts :
    pm.nodes[1284]'(by native_decide) = l15enPmReshape10205 ∧
    pm.nodes[1285]'(by native_decide) = l15enPmReshape10206 ∧
    pm.nodes[1286]'(by native_decide) = l15enPmReshape10211 ∧
    pm.nodes[1287]'(by native_decide) = l15enPmReshape10212 ∧
    pm.nodes[1288]'(by native_decide) = l15enPmLinear10215 ∧
    pm.nodes[1289]'(by native_decide) = l15enPmLinear10216 ∧
    pm.nodes[1290]'(by native_decide) = l15enPmView10225 ∧
    pm.nodes[1291]'(by native_decide) = l15enPmView10226 ∧
    pm.nodes[1292]'(by native_decide) = l15enPmFloat10229 ∧
    pm.nodes[1293]'(by native_decide) = l15enPmFloat10230 ∧
    pm.nodes[1294]'(by native_decide) = l15enPmAdd10233 ∧
    pm.nodes[1295]'(by native_decide) = l15enPmAdd10234 ∧
    pm.nodes[1296]'(by native_decide) = l15enPmMulti2R0 ∧
    pm.nodes[1297]'(by native_decide) = l15enPmMulti2R1 ∧
    pm.nodes[1298]'(by native_decide) = l15enPmRms10237 ∧
    pm.nodes[1299]'(by native_decide) = l15enPmRms10238 ∧
    pm.nodes[1300]'(by native_decide) = l15enPmMulti5R0 ∧
    pm.nodes[1301]'(by native_decide) = l15enPmMulti5R1 := by
  native_decide

private theorem l15en_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l15en_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l15en_weights_not_written :
    (∀ n ∈ sm.nodes, 5497 ∉ n.outs ∧ 5502 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5497 ∉ n.outs ∧ 5502 ∉ n.outs) := by
  native_decide

private theorem l15en_w5497_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5497 ∉ n.outs := by
  intro n hn
  exact (l15en_weights_not_written.1 n (List.mem_of_mem_drop hn)).1

private theorem l15en_w5497_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5497 ∉ n.outs := by
  intro n hn
  exact (l15en_weights_not_written.2 n (List.mem_of_mem_drop hn)).1

private theorem l15en_w5502_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5502 ∉ n.outs := by
  intro n hn
  exact (l15en_weights_not_written.1 n (List.mem_of_mem_drop hn)).2

private theorem l15en_w5502_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5502 ∉ n.outs := by
  intro n hn
  exact (l15en_weights_not_written.2 n (List.mem_of_mem_drop hn)).2

set_option maxRecDepth 1000000 in
private theorem l15en_cu_not_written :
    ∀ n ∈ pm.nodes, 5443 ∉ n.outs ∧ 5492 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l15en_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(612, 5495), (611, 5494), (613, 5496), (614, 5498), (615, 5499), (616,
      5500), (617, 5501), (616, 8260), (618, 8264), (618, 8268), (619, 5503),
      (620, 8275), (620, 8279), (620, 8283), (620, 8287), (620, 8291)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l15en_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1285, 10205), (1284, 10203), (1286, 10206), (1285, 10204), (1287, 10211),
      (1286, 10205), (1288, 10212), (1287, 10206), (1289, 10215), (1288, 10211),
      (1290, 10216), (1289, 10212), (1291, 10225), (1290, 10215), (1292, 10226),
      (1291, 10216), (1293, 10229), (1292, 10225), (1294, 10230), (1293, 10226),
      (1295, 10233), (1294, 16207), (1294, 10229), (1296, 10234), (1295, 16215),
      (1295, 10230), (1297, 16219), (1297, 16223), (1296, 10233), (1298, 16227),
      (1298, 16231), (1297, 10234), (1299, 10237), (1298, 16219), (1300, 10238),
      (1299, 16227), (1301, 16238), (1301, 16242), (1301, 16246), (1301, 16250),
      (1301, 16254), (1300, 10237), (1302, 16261), (1302, 16265), (1302, 16269),
      (1302, 16273), (1302, 16277), (1301, 10238)]) :
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
private theorem l15en_red_sm5495 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5495 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5494) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 611 l15enSmReshape5495
    5494 5495 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l15en_sm_node_facts.1 ?_
    (l15en_nonempty_sm 612) (l15en_sm_not_written 612 5495 (by decide))
    (l15en_nonempty_sm 611) (l15en_sm_not_written 611 5494 (by decide))
  intro s
  unfold l15enSmReshape5495
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5494 5495 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10205 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10205 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10203) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1284 l15enPmReshape10205
    10203 10205 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l15en_pm_node_facts.1 ?_
    (l15en_nonempty_pm 1285) (l15en_pm_not_written 1285 10205 (by decide))
    (l15en_nonempty_pm 1284) (l15en_pm_not_written 1284 10203 (by decide))
  intro s
  unfold l15enPmReshape10205
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10203 10205 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10206 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10206 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10204) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1285 l15enPmReshape10206
    10204 10206 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l15en_pm_node_facts.2.1 ?_
    (l15en_nonempty_pm 1286) (l15en_pm_not_written 1286 10206 (by decide))
    (l15en_nonempty_pm 1285) (l15en_pm_not_written 1285 10204 (by decide))
  intro s
  unfold l15enPmReshape10206
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10204 10206 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_sm5496 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5496 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5495) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 612 l15enSmReshape5496
    5495 5496 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l15en_sm_node_facts.2.1 ?_
    (l15en_nonempty_sm 613) (l15en_sm_not_written 613 5496 (by decide))
    (l15en_nonempty_sm 612) (l15en_sm_not_written 612 5495 (by decide))
  intro s
  unfold l15enSmReshape5496
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5495 5496 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10211 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10211 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10205) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1286 l15enPmReshape10211
    10205 10211 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l15en_pm_node_facts.2.2.1 ?_
    (l15en_nonempty_pm 1287) (l15en_pm_not_written 1287 10211 (by decide))
    (l15en_nonempty_pm 1286) (l15en_pm_not_written 1286 10205 (by decide))
  intro s
  unfold l15enPmReshape10211
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10205 10211 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10212 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10212 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10206) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1287 l15enPmReshape10212
    10206 10212 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l15en_pm_node_facts.2.2.2.1 ?_
    (l15en_nonempty_pm 1288) (l15en_pm_not_written 1288 10212 (by decide))
    (l15en_nonempty_pm 1287) (l15en_pm_not_written 1287 10206 (by decide))
  intro s
  unfold l15enPmReshape10212
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10206 10212 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_sm5498 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5498 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5496)
        (denoteGraphDistributedFaithful sm initSM 5497) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 613 l15enSmLinear5498
    5496 5497 5498 fw_linear
    (by native_decide) l15en_sm_node_facts.2.2.1 ?_
    (l15en_nonempty_sm 614) (l15en_sm_not_written 614 5498 (by decide))
    (l15en_nonempty_sm 613) (l15en_sm_not_written 613 5496 (by decide))
    (l15en_w5497_sm_drop 613)
  intro s
  unfold l15enSmLinear5498
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5496 5497 5498

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10215 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10215 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10211)
        (denoteGraphDistributedFaithful pm initPM 5497) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1288 l15enPmLinear10215
    10211 5497 10215 fw_linear
    (by native_decide) l15en_pm_node_facts.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1289) (l15en_pm_not_written 1289 10215 (by decide))
    (l15en_nonempty_pm 1288) (l15en_pm_not_written 1288 10211 (by decide))
    (l15en_w5497_pm_drop 1288)
  intro s
  unfold l15enPmLinear10215
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10211 5497 10215

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10216 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10216 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10212)
        (denoteGraphDistributedFaithful pm initPM 5497) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1289 l15enPmLinear10216
    10212 5497 10216 fw_linear
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1290) (l15en_pm_not_written 1290 10216 (by decide))
    (l15en_nonempty_pm 1289) (l15en_pm_not_written 1289 10212 (by decide))
    (l15en_w5497_pm_drop 1289)
  intro s
  unfold l15enPmLinear10216
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10212 5497 10216

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_sm5499 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5499 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5498) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 614 l15enSmView5499
    5498 5499 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l15en_sm_node_facts.2.2.2.1 ?_
    (l15en_nonempty_sm 615) (l15en_sm_not_written 615 5499 (by decide))
    (l15en_nonempty_sm 614) (l15en_sm_not_written 614 5498 (by decide))
  intro s
  unfold l15enSmView5499
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5498 5499

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10225 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10225 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10215) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1290 l15enPmView10225
    10215 10225 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1291) (l15en_pm_not_written 1291 10225 (by decide))
    (l15en_nonempty_pm 1290) (l15en_pm_not_written 1290 10215 (by decide))
  intro s
  unfold l15enPmView10225
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 10215 10225

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10226 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10226 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10216) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1291 l15enPmView10226
    10216 10226 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1292) (l15en_pm_not_written 1292 10226 (by decide))
    (l15en_nonempty_pm 1291) (l15en_pm_not_written 1291 10216 (by decide))
  intro s
  unfold l15enPmView10226
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 10216 10226

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_sm5500 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5500 =
      denoteGraphDistributedFaithful sm initSM 5499 := by
  have h := denoteGraphDistributedFaithful_reduce1 sm initSM 615 l15enSmFloat5500
    5499 5500 id
    (by native_decide) l15en_sm_node_facts.2.2.2.2.1 ?_
    (l15en_nonempty_sm 616) (l15en_sm_not_written 616 5500 (by decide))
    (l15en_nonempty_sm 615) (l15en_sm_not_written 615 5499 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l15enSmFloat5500
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out sm s 0 5499 5500 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10229 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10229 =
      denoteGraphDistributedFaithful pm initPM 10225 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1292 l15enPmFloat10229
    10225 10229 id
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1293) (l15en_pm_not_written 1293 10229 (by decide))
    (l15en_nonempty_pm 1292) (l15en_pm_not_written 1292 10225 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l15enPmFloat10229
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 0 10225 10229 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10230 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10230 =
      denoteGraphDistributedFaithful pm initPM 10226 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1293 l15enPmFloat10230
    10226 10230 id
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1294) (l15en_pm_not_written 1294 10230 (by decide))
    (l15en_nonempty_pm 1293) (l15en_pm_not_written 1293 10226 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l15enPmFloat10230
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 1 10226 10230 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_sm5501 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5501 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8260)
        (denoteGraphDistributedFaithful sm initSM 5500) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 616 l15enSmAdd5501
    8260 5500 5501 elemwiseAdd
    (by native_decide) l15en_sm_node_facts.2.2.2.2.2.1 ?_
    (l15en_nonempty_sm 617) (l15en_sm_not_written 617 5501 (by decide))
    (l15en_nonempty_sm 616) (l15en_sm_not_written 616 8260 (by decide))
    (l15en_sm_not_written 616 5500 (by decide))
  intro s
  unfold l15enSmAdd5501
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8260 5500 5501

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10233 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10233 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16207)
        (denoteGraphDistributedFaithful pm initPM 10229) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1294 l15enPmAdd10233
    16207 10229 10233 elemwiseAdd
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1295) (l15en_pm_not_written 1295 10233 (by decide))
    (l15en_nonempty_pm 1294) (l15en_pm_not_written 1294 16207 (by decide))
    (l15en_pm_not_written 1294 10229 (by decide))
  intro s
  unfold l15enPmAdd10233
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16207 10229 10233

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10234 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10234 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16215)
        (denoteGraphDistributedFaithful pm initPM 10230) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1295 l15enPmAdd10234
    16215 10230 10234 elemwiseAdd
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1296) (l15en_pm_not_written 1296 10234 (by decide))
    (l15en_nonempty_pm 1295) (l15en_pm_not_written 1295 16215 (by decide))
    (l15en_pm_not_written 1295 10230 (by decide))
  intro s
  unfold l15enPmAdd10234
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16215 10230 10234

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_sm8264 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8264 =
      denoteGraphDistributedFaithful sm initSM 5501 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 617 l15enSmMulti2
    5501 8264 (fun x => x)
    (by native_decide) l15en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_sm 618) (l15en_sm_not_written 618 8264 (by decide))
    (l15en_nonempty_sm 617) (l15en_sm_not_written 617 5501 (by decide))
  intro s
  unfold l15enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5501 8264 8268

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_sm8268 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8268 =
      denoteGraphDistributedFaithful sm initSM 5501 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 617 l15enSmMulti2
    5501 8268 (fun x => x)
    (by native_decide) l15en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_sm 618) (l15en_sm_not_written 618 8268 (by decide))
    (l15en_nonempty_sm 617) (l15en_sm_not_written 617 5501 (by decide))
  intro s
  unfold l15enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5501 8264 8268 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16219 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16219 =
      denoteGraphDistributedFaithful pm initPM 10233 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1296 l15enPmMulti2R0
    10233 16219 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1297) (l15en_pm_not_written 1297 16219 (by decide))
    (l15en_nonempty_pm 1296) (l15en_pm_not_written 1296 10233 (by decide))
  intro s
  unfold l15enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 10233 16219 16223

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16223 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16223 =
      denoteGraphDistributedFaithful pm initPM 10233 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1296 l15enPmMulti2R0
    10233 16223 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1297) (l15en_pm_not_written 1297 16223 (by decide))
    (l15en_nonempty_pm 1296) (l15en_pm_not_written 1296 10233 (by decide))
  intro s
  unfold l15enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 10233 16219 16223 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16227 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16227 =
      denoteGraphDistributedFaithful pm initPM 10234 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1297 l15enPmMulti2R1
    10234 16227 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1298) (l15en_pm_not_written 1298 16227 (by decide))
    (l15en_nonempty_pm 1297) (l15en_pm_not_written 1297 10234 (by decide))
  intro s
  unfold l15enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 10234 16227 16231

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16231 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16231 =
      denoteGraphDistributedFaithful pm initPM 10234 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1297 l15enPmMulti2R1
    10234 16231 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1298) (l15en_pm_not_written 1298 16231 (by decide))
    (l15en_nonempty_pm 1297) (l15en_pm_not_written 1297 10234 (by decide))
  intro s
  unfold l15enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 10234 16227 16231 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_sm5503 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5503 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8264)
        (denoteGraphDistributedFaithful sm initSM 5502) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 618 l15enSmRms5503
    8264 5502 5503 fw_rms_norm
    (by native_decide) l15en_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_sm 619) (l15en_sm_not_written 619 5503 (by decide))
    (l15en_nonempty_sm 618) (l15en_sm_not_written 618 8264 (by decide))
    (l15en_w5502_sm_drop 618)
  intro s
  unfold l15enSmRms5503
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8264 5502 5503

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10237 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10237 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16219)
        (denoteGraphDistributedFaithful pm initPM 5502) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1298 l15enPmRms10237
    16219 5502 10237 fw_rms_norm
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1299) (l15en_pm_not_written 1299 10237 (by decide))
    (l15en_nonempty_pm 1298) (l15en_pm_not_written 1298 16219 (by decide))
    (l15en_w5502_pm_drop 1298)
  intro s
  unfold l15enPmRms10237
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16219 5502 10237

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm10238 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10238 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16227)
        (denoteGraphDistributedFaithful pm initPM 5502) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1299 l15enPmRms10238
    16227 5502 10238 fw_rms_norm
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1300) (l15en_pm_not_written 1300 10238 (by decide))
    (l15en_nonempty_pm 1299) (l15en_pm_not_written 1299 16227 (by decide))
    (l15en_w5502_pm_drop 1299)
  intro s
  unfold l15enPmRms10238
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16227 5502 10238

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_sm8275 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8275 =
      denoteGraphDistributedFaithful sm initSM 5503 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 619 l15enSmMulti5
    5503 8275 (fun x => x)
    (by native_decide) l15en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l15en_nonempty_sm 620) (l15en_sm_not_written 620 8275 (by decide))
    (l15en_nonempty_sm 619) (l15en_sm_not_written 619 5503 (by decide))
  intro s
  unfold l15enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l15en_multiref5_first_out sm s 0 5503 8275 8279 8283 8287 8291

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_sm8279 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8279 =
      denoteGraphDistributedFaithful sm initSM 5503 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 619 l15enSmMulti5
    5503 8279 (fun x => x)
    (by native_decide) l15en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l15en_nonempty_sm 620) (l15en_sm_not_written 620 8279 (by decide))
    (l15en_nonempty_sm 619) (l15en_sm_not_written 619 5503 (by decide))
  intro s
  unfold l15enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out sm s 0 5503 8275 8279 8283 8287 8291
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_sm8283 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8283 =
      denoteGraphDistributedFaithful sm initSM 5503 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 619 l15enSmMulti5
    5503 8283 (fun x => x)
    (by native_decide) l15en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l15en_nonempty_sm 620) (l15en_sm_not_written 620 8283 (by decide))
    (l15en_nonempty_sm 619) (l15en_sm_not_written 619 5503 (by decide))
  intro s
  unfold l15enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out sm s 0 5503 8275 8279 8283 8287 8291
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_sm8287 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8287 =
      denoteGraphDistributedFaithful sm initSM 5503 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 619 l15enSmMulti5
    5503 8287 (fun x => x)
    (by native_decide) l15en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l15en_nonempty_sm 620) (l15en_sm_not_written 620 8287 (by decide))
    (l15en_nonempty_sm 619) (l15en_sm_not_written 619 5503 (by decide))
  intro s
  unfold l15enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out sm s 0 5503 8275 8279 8283 8287 8291
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_sm8291 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8291 =
      denoteGraphDistributedFaithful sm initSM 5503 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 619 l15enSmMulti5
    5503 8291 (fun x => x)
    (by native_decide) l15en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l15en_nonempty_sm 620) (l15en_sm_not_written 620 8291 (by decide))
    (l15en_nonempty_sm 619) (l15en_sm_not_written 619 5503 (by decide))
  intro s
  unfold l15enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out sm s 0 5503 8275 8279 8283 8287 8291
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16238 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16238 =
      denoteGraphDistributedFaithful pm initPM 10237 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1300 l15enPmMulti5R0
    10237 16238 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1301) (l15en_pm_not_written 1301 16238 (by decide))
    (l15en_nonempty_pm 1300) (l15en_pm_not_written 1300 10237 (by decide))
  intro s
  unfold l15enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l15en_multiref5_first_out pm s 0 10237 16238 16242 16246 16250 16254

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16242 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16242 =
      denoteGraphDistributedFaithful pm initPM 10237 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1300 l15enPmMulti5R0
    10237 16242 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1301) (l15en_pm_not_written 1301 16242 (by decide))
    (l15en_nonempty_pm 1300) (l15en_pm_not_written 1300 10237 (by decide))
  intro s
  unfold l15enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 0 10237 16238 16242 16246 16250 16254
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16246 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16246 =
      denoteGraphDistributedFaithful pm initPM 10237 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1300 l15enPmMulti5R0
    10237 16246 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1301) (l15en_pm_not_written 1301 16246 (by decide))
    (l15en_nonempty_pm 1300) (l15en_pm_not_written 1300 10237 (by decide))
  intro s
  unfold l15enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 0 10237 16238 16242 16246 16250 16254
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16250 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16250 =
      denoteGraphDistributedFaithful pm initPM 10237 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1300 l15enPmMulti5R0
    10237 16250 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1301) (l15en_pm_not_written 1301 16250 (by decide))
    (l15en_nonempty_pm 1300) (l15en_pm_not_written 1300 10237 (by decide))
  intro s
  unfold l15enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 0 10237 16238 16242 16246 16250 16254
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16254 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16254 =
      denoteGraphDistributedFaithful pm initPM 10237 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1300 l15enPmMulti5R0
    10237 16254 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15en_nonempty_pm 1301) (l15en_pm_not_written 1301 16254 (by decide))
    (l15en_nonempty_pm 1300) (l15en_pm_not_written 1300 10237 (by decide))
  intro s
  unfold l15enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 0 10237 16238 16242 16246 16250 16254
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16261 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16261 =
      denoteGraphDistributedFaithful pm initPM 10238 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1301 l15enPmMulti5R1
    10238 16261 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l15en_nonempty_pm 1302) (l15en_pm_not_written 1302 16261 (by decide))
    (l15en_nonempty_pm 1301) (l15en_pm_not_written 1301 10238 (by decide))
  intro s
  unfold l15enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l15en_multiref5_first_out pm s 1 10238 16261 16265 16269 16273 16277

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16265 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16265 =
      denoteGraphDistributedFaithful pm initPM 10238 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1301 l15enPmMulti5R1
    10238 16265 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l15en_nonempty_pm 1302) (l15en_pm_not_written 1302 16265 (by decide))
    (l15en_nonempty_pm 1301) (l15en_pm_not_written 1301 10238 (by decide))
  intro s
  unfold l15enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 1 10238 16261 16265 16269 16273 16277
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16269 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16269 =
      denoteGraphDistributedFaithful pm initPM 10238 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1301 l15enPmMulti5R1
    10238 16269 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l15en_nonempty_pm 1302) (l15en_pm_not_written 1302 16269 (by decide))
    (l15en_nonempty_pm 1301) (l15en_pm_not_written 1301 10238 (by decide))
  intro s
  unfold l15enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 1 10238 16261 16265 16269 16273 16277
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16273 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16273 =
      denoteGraphDistributedFaithful pm initPM 10238 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1301 l15enPmMulti5R1
    10238 16273 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l15en_nonempty_pm 1302) (l15en_pm_not_written 1302 16273 (by decide))
    (l15en_nonempty_pm 1301) (l15en_pm_not_written 1301 10238 (by decide))
  intro s
  unfold l15enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 1 10238 16261 16265 16269 16273 16277
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15en_red_pm16277 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16277 =
      denoteGraphDistributedFaithful pm initPM 10238 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1301 l15enPmMulti5R1
    10238 16277 (fun x => x)
    (by native_decide) l15en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l15en_nonempty_pm 1302) (l15en_pm_not_written 1302 16277 (by decide))
    (l15en_nonempty_pm 1301) (l15en_pm_not_written 1301 10238 (by decide))
  intro s
  unfold l15enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 1 10238 16261 16265 16269 16273 16277
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5495 (`FW_reshape` of 5494).
theorem recon_zigzagGoal_5495_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5495)
      (denoteGraphDistributedFaithful pm initPM 10205)
      (denoteGraphDistributedFaithful pm initPM 10206)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5494_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15en_red_sm5495 initSM, l15en_red_pm10205 initPM, l15en_red_pm10206 initPM]
  exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hparent (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5496 (`FW_reshape` of 5495).
theorem recon_zigzagGoal_5496_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5496)
      (denoteGraphDistributedFaithful pm initPM 10211)
      (denoteGraphDistributedFaithful pm initPM 10212)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5495_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15en_red_sm5496 initSM, l15en_red_pm10211 initPM, l15en_red_pm10212 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5498 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5498_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5498)
      (denoteGraphDistributedFaithful pm initPM 10215)
      (denoteGraphDistributedFaithful pm initPM 10216)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5496_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5497 = initPM 5497 :=
    recon_weight initSM initPM hInit initGoal_5497 (by native_decide) 5497
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5497 = initSM 5497 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5497
      layer1_sm_nodes_nonempty (fun n hn => (l15en_weights_not_written.1 n hn).1)
  have hpw : denoteGraphDistributedFaithful pm initPM 5497 = initPM 5497 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5497
      layer1_pm_nodes_nonempty (fun n hn => (l15en_weights_not_written.2 n hn).1)
  have hw : denoteGraphDistributedFaithful sm initSM 5497 =
      denoteGraphDistributedFaithful pm initPM 5497 := by
    rw [hsw, hpw]; exact hwInit
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5497).shape =
      [1024, 1024] := by
    rw [hpw]
    exact hPM 5497 [1024, 1024] (by native_decide)
  rw [l15en_red_sm5498 initSM, l15en_red_pm10215 initPM, l15en_red_pm10216 initPM, hw]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5499 (`FW_view` of 5498).
theorem recon_zigzagGoal_5499_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5499)
      (denoteGraphDistributedFaithful pm initPM 10225)
      (denoteGraphDistributedFaithful pm initPM 10226)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5498_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15en_red_sm5499 initSM, l15en_red_pm10225 initPM, l15en_red_pm10226 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5500 (`FW_float` of 5499).
theorem recon_zigzagGoal_5500_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5500)
      (denoteGraphDistributedFaithful pm initPM 10229)
      (denoteGraphDistributedFaithful pm initPM 10230)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5499_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15en_red_sm5500 initSM, l15en_red_pm10229 initPM, l15en_red_pm10230 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5501 (residual `FW_add` of the
-- cross-layer bypass 8260 and 5500).
theorem recon_zigzagGoal_5501_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5501)
      (denoteGraphDistributedFaithful pm initPM 10233)
      (denoteGraphDistributedFaithful pm initPM 10234)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8260_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5500_faithful initSM initPM hSM hPM hInit hValues hCu
  have pmFinal (tid : Tid) (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hw
  have h5443_5492 : denoteGraphDistributedFaithful pm initPM 5443 =
      denoteGraphDistributedFaithful pm initPM 5492 := by
    rw [pmFinal 5443 (fun n hn => (l15en_cu_not_written n hn).1),
      pmFinal 5492 (fun n hn => (l15en_cu_not_written n hn).2)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  rw [h5443_5492] at hA
  rw [l15en_red_sm5501 initSM, l15en_red_pm10233 initPM, l15en_red_pm10234 initPM]
  exact Zigzag2Rel.add 2048 1024 hA hB (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8264 (2-way multiref, position 0).
theorem recon_zigzagGoal_8264_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8264)
      (denoteGraphDistributedFaithful pm initPM 16219)
      (denoteGraphDistributedFaithful pm initPM 16227)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5501_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15en_red_sm8264 initSM, l15en_red_pm16219 initPM, l15en_red_pm16227 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8268 (2-way multiref, position 1).
theorem recon_zigzagGoal_8268_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8268)
      (denoteGraphDistributedFaithful pm initPM 16223)
      (denoteGraphDistributedFaithful pm initPM 16231)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5501_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15en_red_sm8268 initSM, l15en_red_pm16223 initPM, l15en_red_pm16231 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5503 (`FW_rms_norm` of 8264 with
-- the replicated weight 5502).
theorem recon_zigzagGoal_5503_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5503)
      (denoteGraphDistributedFaithful pm initPM 10237)
      (denoteGraphDistributedFaithful pm initPM 10238)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8264_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5502 = initPM 5502 :=
    recon_weight initSM initPM hInit initGoal_5502 (by native_decide) 5502
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5502 = initSM 5502 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5502
      layer1_sm_nodes_nonempty (fun n hn => (l15en_weights_not_written.1 n hn).2)
  have hpw : denoteGraphDistributedFaithful pm initPM 5502 = initPM 5502 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5502
      layer1_pm_nodes_nonempty (fun n hn => (l15en_weights_not_written.2 n hn).2)
  have hw : denoteGraphDistributedFaithful sm initSM 5502 =
      denoteGraphDistributedFaithful pm initPM 5502 := by
    rw [hsw, hpw]; exact hwInit
  rw [l15en_red_sm5503 initSM, l15en_red_pm10237 initPM, l15en_red_pm10238 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8275 (5-way multiref, position 0).
theorem recon_zigzagGoal_8275_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8275)
      (denoteGraphDistributedFaithful pm initPM 16238)
      (denoteGraphDistributedFaithful pm initPM 16261)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5503_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15en_red_sm8275 initSM, l15en_red_pm16238 initPM, l15en_red_pm16261 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8279 (5-way multiref, position 1).
theorem recon_zigzagGoal_8279_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8279)
      (denoteGraphDistributedFaithful pm initPM 16242)
      (denoteGraphDistributedFaithful pm initPM 16265)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5503_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15en_red_sm8279 initSM, l15en_red_pm16242 initPM, l15en_red_pm16265 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8283 (5-way multiref, position 2).
theorem recon_zigzagGoal_8283_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8283)
      (denoteGraphDistributedFaithful pm initPM 16246)
      (denoteGraphDistributedFaithful pm initPM 16269)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5503_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15en_red_sm8283 initSM, l15en_red_pm16246 initPM, l15en_red_pm16269 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8287 (5-way multiref, position 3).
theorem recon_zigzagGoal_8287_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8287)
      (denoteGraphDistributedFaithful pm initPM 16250)
      (denoteGraphDistributedFaithful pm initPM 16273)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5503_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15en_red_sm8287 initSM, l15en_red_pm16250 initPM, l15en_red_pm16273 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8291 (5-way multiref, position 4).
theorem recon_zigzagGoal_8291_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8291)
      (denoteGraphDistributedFaithful pm initPM 16254)
      (denoteGraphDistributedFaithful pm initPM 16277)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5503_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15en_red_sm8291 initSM, l15en_red_pm16254 initPM, l15en_red_pm16277 initPM]
  exact hparent

end
end TrainVerify.Denote.GeneratedPatterns
