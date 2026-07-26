/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L16FaithfulZigzagAttention
import denote.yoco_goals.L15FaithfulBlockTail
import denote.yoco_goals.L12FaithfulRouterEntry

/-!
# Faithful zigzag relations for the block-4 entry segment

Continuation of `recon_zigzagGoal_5543_faithful` (block-4 cross-decoder
attention) through the block-4 entry segment:

* SM 646: `FW_reshape [5543] → [5544]`   (PM 1354/1355: `10375 → 10377`, `10376 → 10378`)
* SM 647: `FW_reshape [5544] → [5545]`   (PM 1356/1357: `10377 → 10383`, `10378 → 10384`)
* SM 648: `FW_mix_precision_linear [5545, 5546] → [5547]`
                                          (PM 1358/1359 with replicated weight 5546)
* SM 649: `FW_view [5547] → [5548]`      (PM 1360/1361)
* SM 650: `FW_float [5548] → [5549]`     (PM 1362/1363)
* SM 651: `FW_add [8299, 5549] → [5550]` (PM 1364/1365 with bypass 16285/16293)
* SM 652: `FW_multiref [5550] → [8303, 8307]`
                                          (PM 1366: `[16297, 16301]`, PM 1367: `[16305, 16309]`)
* SM 653: `FW_rms_norm [8303, 5551] → [5552]` (PM 1368/1369, replicated weight 5551)
* SM 654: `FW_multiref [5552] → [8314, 8318, 8322, 8326, 8330]`
                                          (PM 1370: `[16316, 16320, 16324, 16328, 16332]`,
                                           PM 1371: `[16339, 16343, 16347, 16351, 16355]`)

All relations are stated against the block-4 cumulative-sequence metadata tensor
`5541` (the same cu slot used by `recon_zigzagGoal_5543_faithful`).
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

private theorem l16en_multiref5_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 t4 t5 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := [t1, t2, t3, t4, t5], params := [5] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3, t4, t5].zip (List.replicate 5 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ### Node literals -/

private def l16enSmReshape5544 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5543], outs := [5544],
    params := [4096, 1024] }
private def l16enSmReshape5545 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5544], outs := [5545],
    params := [4096, 1024] }
private def l16enSmLinear5547 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5545, 5546],
    outs := [5547] }
private def l16enSmView5548 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5547], outs := [5548],
    params := [4096, 1024] }
private def l16enSmFloat5549 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5548], outs := [5549] }
private def l16enSmAdd5550 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8299, 5549], outs := [5550] }
private def l16enSmMulti2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5550], outs := [8303, 8307],
    params := [2] }
private def l16enSmRms5552 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8303, 5551], outs := [5552] }
private def l16enSmMulti5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5552],
    outs := [8314, 8318, 8322, 8326, 8330], params := [5] }

private def l16enPmReshape10377 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10375], outs := [10377],
    params := [2048, 1024] }
private def l16enPmReshape10378 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10376], outs := [10378],
    params := [2048, 1024] }
private def l16enPmReshape10383 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10377], outs := [10383],
    params := [2048, 1024] }
private def l16enPmReshape10384 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10378], outs := [10384],
    params := [2048, 1024] }
private def l16enPmLinear10387 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10383, 5546],
    outs := [10387] }
private def l16enPmLinear10388 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10384, 5546],
    outs := [10388] }
private def l16enPmView10397 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10387], outs := [10397],
    params := [2048, 1024] }
private def l16enPmView10398 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10388], outs := [10398],
    params := [2048, 1024] }
private def l16enPmFloat10401 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10397], outs := [10401] }
private def l16enPmFloat10402 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10398], outs := [10402] }
private def l16enPmAdd10405 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16285, 10401], outs := [10405] }
private def l16enPmAdd10406 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16293, 10402], outs := [10406] }
private def l16enPmMulti2R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10405], outs := [16297, 16301],
    params := [2] }
private def l16enPmMulti2R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10406], outs := [16305, 16309],
    params := [2] }
private def l16enPmRms10409 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16297, 5551], outs := [10409] }
private def l16enPmRms10410 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16305, 5551], outs := [10410] }
private def l16enPmMulti5R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10409],
    outs := [16316, 16320, 16324, 16328, 16332], params := [5] }
private def l16enPmMulti5R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10410],
    outs := [16339, 16343, 16347, 16351, 16355], params := [5] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l16en_sm_node_facts :
    sm.nodes[646]'(by native_decide) = l16enSmReshape5544 ∧
    sm.nodes[647]'(by native_decide) = l16enSmReshape5545 ∧
    sm.nodes[648]'(by native_decide) = l16enSmLinear5547 ∧
    sm.nodes[649]'(by native_decide) = l16enSmView5548 ∧
    sm.nodes[650]'(by native_decide) = l16enSmFloat5549 ∧
    sm.nodes[651]'(by native_decide) = l16enSmAdd5550 ∧
    sm.nodes[652]'(by native_decide) = l16enSmMulti2 ∧
    sm.nodes[653]'(by native_decide) = l16enSmRms5552 ∧
    sm.nodes[654]'(by native_decide) = l16enSmMulti5 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l16en_pm_node_facts :
    pm.nodes[1354]'(by native_decide) = l16enPmReshape10377 ∧
    pm.nodes[1355]'(by native_decide) = l16enPmReshape10378 ∧
    pm.nodes[1356]'(by native_decide) = l16enPmReshape10383 ∧
    pm.nodes[1357]'(by native_decide) = l16enPmReshape10384 ∧
    pm.nodes[1358]'(by native_decide) = l16enPmLinear10387 ∧
    pm.nodes[1359]'(by native_decide) = l16enPmLinear10388 ∧
    pm.nodes[1360]'(by native_decide) = l16enPmView10397 ∧
    pm.nodes[1361]'(by native_decide) = l16enPmView10398 ∧
    pm.nodes[1362]'(by native_decide) = l16enPmFloat10401 ∧
    pm.nodes[1363]'(by native_decide) = l16enPmFloat10402 ∧
    pm.nodes[1364]'(by native_decide) = l16enPmAdd10405 ∧
    pm.nodes[1365]'(by native_decide) = l16enPmAdd10406 ∧
    pm.nodes[1366]'(by native_decide) = l16enPmMulti2R0 ∧
    pm.nodes[1367]'(by native_decide) = l16enPmMulti2R1 ∧
    pm.nodes[1368]'(by native_decide) = l16enPmRms10409 ∧
    pm.nodes[1369]'(by native_decide) = l16enPmRms10410 ∧
    pm.nodes[1370]'(by native_decide) = l16enPmMulti5R0 ∧
    pm.nodes[1371]'(by native_decide) = l16enPmMulti5R1 := by
  native_decide

private theorem l16en_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l16en_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l16en_weights_not_written :
    (∀ n ∈ sm.nodes, 5546 ∉ n.outs ∧ 5551 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5546 ∉ n.outs ∧ 5551 ∉ n.outs) := by
  native_decide

private theorem l16en_w5546_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5546 ∉ n.outs := by
  intro n hn
  exact (l16en_weights_not_written.1 n (List.mem_of_mem_drop hn)).1

private theorem l16en_w5546_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5546 ∉ n.outs := by
  intro n hn
  exact (l16en_weights_not_written.2 n (List.mem_of_mem_drop hn)).1

private theorem l16en_w5551_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5551 ∉ n.outs := by
  intro n hn
  exact (l16en_weights_not_written.1 n (List.mem_of_mem_drop hn)).2

private theorem l16en_w5551_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5551 ∉ n.outs := by
  intro n hn
  exact (l16en_weights_not_written.2 n (List.mem_of_mem_drop hn)).2

set_option maxRecDepth 1000000 in
private theorem l16en_cu_not_written :
    ∀ n ∈ pm.nodes, 5492 ∉ n.outs ∧ 5541 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l16en_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(647, 5544), (646, 5543), (648, 5545), (649, 5547), (650, 5548), (651,
      5549), (652, 5550), (651, 8299), (653, 8303), (653, 8307), (654, 5552),
      (655, 8314), (655, 8318), (655, 8322), (655, 8326), (655, 8330)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l16en_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1355, 10377), (1354, 10375), (1356, 10378), (1355, 10376), (1357, 10383),
      (1356, 10377), (1358, 10384), (1357, 10378), (1359, 10387), (1358, 10383),
      (1360, 10388), (1359, 10384), (1361, 10397), (1360, 10387), (1362, 10398),
      (1361, 10388), (1363, 10401), (1362, 10397), (1364, 10402), (1363, 10398),
      (1365, 10405), (1364, 16285), (1364, 10401), (1366, 10406), (1365, 16293),
      (1365, 10402), (1367, 16297), (1367, 16301), (1366, 10405), (1368, 16305),
      (1368, 16309), (1367, 10406), (1369, 10409), (1368, 16297), (1370, 10410),
      (1369, 16305), (1371, 16316), (1371, 16320), (1371, 16324), (1371, 16328),
      (1371, 16332), (1370, 10409), (1372, 16339), (1372, 16343), (1372, 16347),
      (1372, 16351), (1372, 16355), (1371, 10410)]) :
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
private theorem l16en_red_sm5544 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5544 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5543) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 646 l16enSmReshape5544
    5543 5544 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l16en_sm_node_facts.1 ?_
    (l16en_nonempty_sm 647) (l16en_sm_not_written 647 5544 (by decide))
    (l16en_nonempty_sm 646) (l16en_sm_not_written 646 5543 (by decide))
  intro s
  unfold l16enSmReshape5544
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5543 5544 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10377 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10377 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10375) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1354 l16enPmReshape10377
    10375 10377 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l16en_pm_node_facts.1 ?_
    (l16en_nonempty_pm 1355) (l16en_pm_not_written 1355 10377 (by decide))
    (l16en_nonempty_pm 1354) (l16en_pm_not_written 1354 10375 (by decide))
  intro s
  unfold l16enPmReshape10377
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10375 10377 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10378 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10378 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10376) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1355 l16enPmReshape10378
    10376 10378 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l16en_pm_node_facts.2.1 ?_
    (l16en_nonempty_pm 1356) (l16en_pm_not_written 1356 10378 (by decide))
    (l16en_nonempty_pm 1355) (l16en_pm_not_written 1355 10376 (by decide))
  intro s
  unfold l16enPmReshape10378
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10376 10378 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_sm5545 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5545 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5544) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 647 l16enSmReshape5545
    5544 5545 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l16en_sm_node_facts.2.1 ?_
    (l16en_nonempty_sm 648) (l16en_sm_not_written 648 5545 (by decide))
    (l16en_nonempty_sm 647) (l16en_sm_not_written 647 5544 (by decide))
  intro s
  unfold l16enSmReshape5545
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5544 5545 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10383 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10383 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10377) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1356 l16enPmReshape10383
    10377 10383 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l16en_pm_node_facts.2.2.1 ?_
    (l16en_nonempty_pm 1357) (l16en_pm_not_written 1357 10383 (by decide))
    (l16en_nonempty_pm 1356) (l16en_pm_not_written 1356 10377 (by decide))
  intro s
  unfold l16enPmReshape10383
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10377 10383 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10384 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10384 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10378) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1357 l16enPmReshape10384
    10378 10384 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l16en_pm_node_facts.2.2.2.1 ?_
    (l16en_nonempty_pm 1358) (l16en_pm_not_written 1358 10384 (by decide))
    (l16en_nonempty_pm 1357) (l16en_pm_not_written 1357 10378 (by decide))
  intro s
  unfold l16enPmReshape10384
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10378 10384 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_sm5547 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5547 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5545)
        (denoteGraphDistributedFaithful sm initSM 5546) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 648 l16enSmLinear5547
    5545 5546 5547 fw_linear
    (by native_decide) l16en_sm_node_facts.2.2.1 ?_
    (l16en_nonempty_sm 649) (l16en_sm_not_written 649 5547 (by decide))
    (l16en_nonempty_sm 648) (l16en_sm_not_written 648 5545 (by decide))
    (l16en_w5546_sm_drop 648)
  intro s
  unfold l16enSmLinear5547
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5545 5546 5547

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10387 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10387 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10383)
        (denoteGraphDistributedFaithful pm initPM 5546) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1358 l16enPmLinear10387
    10383 5546 10387 fw_linear
    (by native_decide) l16en_pm_node_facts.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1359) (l16en_pm_not_written 1359 10387 (by decide))
    (l16en_nonempty_pm 1358) (l16en_pm_not_written 1358 10383 (by decide))
    (l16en_w5546_pm_drop 1358)
  intro s
  unfold l16enPmLinear10387
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10383 5546 10387

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10388 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10388 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10384)
        (denoteGraphDistributedFaithful pm initPM 5546) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1359 l16enPmLinear10388
    10384 5546 10388 fw_linear
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1360) (l16en_pm_not_written 1360 10388 (by decide))
    (l16en_nonempty_pm 1359) (l16en_pm_not_written 1359 10384 (by decide))
    (l16en_w5546_pm_drop 1359)
  intro s
  unfold l16enPmLinear10388
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10384 5546 10388

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_sm5548 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5548 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5547) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 649 l16enSmView5548
    5547 5548 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l16en_sm_node_facts.2.2.2.1 ?_
    (l16en_nonempty_sm 650) (l16en_sm_not_written 650 5548 (by decide))
    (l16en_nonempty_sm 649) (l16en_sm_not_written 649 5547 (by decide))
  intro s
  unfold l16enSmView5548
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5547 5548

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10397 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10397 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10387) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1360 l16enPmView10397
    10387 10397 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1361) (l16en_pm_not_written 1361 10397 (by decide))
    (l16en_nonempty_pm 1360) (l16en_pm_not_written 1360 10387 (by decide))
  intro s
  unfold l16enPmView10397
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 10387 10397

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10398 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10398 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10388) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1361 l16enPmView10398
    10388 10398 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1362) (l16en_pm_not_written 1362 10398 (by decide))
    (l16en_nonempty_pm 1361) (l16en_pm_not_written 1361 10388 (by decide))
  intro s
  unfold l16enPmView10398
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 10388 10398

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_sm5549 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5549 =
      denoteGraphDistributedFaithful sm initSM 5548 := by
  have h := denoteGraphDistributedFaithful_reduce1 sm initSM 650 l16enSmFloat5549
    5548 5549 id
    (by native_decide) l16en_sm_node_facts.2.2.2.2.1 ?_
    (l16en_nonempty_sm 651) (l16en_sm_not_written 651 5549 (by decide))
    (l16en_nonempty_sm 650) (l16en_sm_not_written 650 5548 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l16enSmFloat5549
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out sm s 0 5548 5549 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10401 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10401 =
      denoteGraphDistributedFaithful pm initPM 10397 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1362 l16enPmFloat10401
    10397 10401 id
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1363) (l16en_pm_not_written 1363 10401 (by decide))
    (l16en_nonempty_pm 1362) (l16en_pm_not_written 1362 10397 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l16enPmFloat10401
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 0 10397 10401 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10402 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10402 =
      denoteGraphDistributedFaithful pm initPM 10398 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1363 l16enPmFloat10402
    10398 10402 id
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1364) (l16en_pm_not_written 1364 10402 (by decide))
    (l16en_nonempty_pm 1363) (l16en_pm_not_written 1363 10398 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l16enPmFloat10402
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 1 10398 10402 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_sm5550 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5550 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8299)
        (denoteGraphDistributedFaithful sm initSM 5549) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 651 l16enSmAdd5550
    8299 5549 5550 elemwiseAdd
    (by native_decide) l16en_sm_node_facts.2.2.2.2.2.1 ?_
    (l16en_nonempty_sm 652) (l16en_sm_not_written 652 5550 (by decide))
    (l16en_nonempty_sm 651) (l16en_sm_not_written 651 8299 (by decide))
    (l16en_sm_not_written 651 5549 (by decide))
  intro s
  unfold l16enSmAdd5550
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8299 5549 5550

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10405 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10405 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16285)
        (denoteGraphDistributedFaithful pm initPM 10401) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1364 l16enPmAdd10405
    16285 10401 10405 elemwiseAdd
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1365) (l16en_pm_not_written 1365 10405 (by decide))
    (l16en_nonempty_pm 1364) (l16en_pm_not_written 1364 16285 (by decide))
    (l16en_pm_not_written 1364 10401 (by decide))
  intro s
  unfold l16enPmAdd10405
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16285 10401 10405

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10406 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10406 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16293)
        (denoteGraphDistributedFaithful pm initPM 10402) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1365 l16enPmAdd10406
    16293 10402 10406 elemwiseAdd
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1366) (l16en_pm_not_written 1366 10406 (by decide))
    (l16en_nonempty_pm 1365) (l16en_pm_not_written 1365 16293 (by decide))
    (l16en_pm_not_written 1365 10402 (by decide))
  intro s
  unfold l16enPmAdd10406
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16293 10402 10406

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_sm8303 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8303 =
      denoteGraphDistributedFaithful sm initSM 5550 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 652 l16enSmMulti2
    5550 8303 (fun x => x)
    (by native_decide) l16en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_sm 653) (l16en_sm_not_written 653 8303 (by decide))
    (l16en_nonempty_sm 652) (l16en_sm_not_written 652 5550 (by decide))
  intro s
  unfold l16enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5550 8303 8307

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_sm8307 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8307 =
      denoteGraphDistributedFaithful sm initSM 5550 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 652 l16enSmMulti2
    5550 8307 (fun x => x)
    (by native_decide) l16en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_sm 653) (l16en_sm_not_written 653 8307 (by decide))
    (l16en_nonempty_sm 652) (l16en_sm_not_written 652 5550 (by decide))
  intro s
  unfold l16enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5550 8303 8307 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16297 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16297 =
      denoteGraphDistributedFaithful pm initPM 10405 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1366 l16enPmMulti2R0
    10405 16297 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1367) (l16en_pm_not_written 1367 16297 (by decide))
    (l16en_nonempty_pm 1366) (l16en_pm_not_written 1366 10405 (by decide))
  intro s
  unfold l16enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 10405 16297 16301

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16301 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16301 =
      denoteGraphDistributedFaithful pm initPM 10405 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1366 l16enPmMulti2R0
    10405 16301 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1367) (l16en_pm_not_written 1367 16301 (by decide))
    (l16en_nonempty_pm 1366) (l16en_pm_not_written 1366 10405 (by decide))
  intro s
  unfold l16enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 10405 16297 16301 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16305 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16305 =
      denoteGraphDistributedFaithful pm initPM 10406 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1367 l16enPmMulti2R1
    10406 16305 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1368) (l16en_pm_not_written 1368 16305 (by decide))
    (l16en_nonempty_pm 1367) (l16en_pm_not_written 1367 10406 (by decide))
  intro s
  unfold l16enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 10406 16305 16309

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16309 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16309 =
      denoteGraphDistributedFaithful pm initPM 10406 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1367 l16enPmMulti2R1
    10406 16309 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1368) (l16en_pm_not_written 1368 16309 (by decide))
    (l16en_nonempty_pm 1367) (l16en_pm_not_written 1367 10406 (by decide))
  intro s
  unfold l16enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 10406 16305 16309 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_sm5552 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5552 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8303)
        (denoteGraphDistributedFaithful sm initSM 5551) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 653 l16enSmRms5552
    8303 5551 5552 fw_rms_norm
    (by native_decide) l16en_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_sm 654) (l16en_sm_not_written 654 5552 (by decide))
    (l16en_nonempty_sm 653) (l16en_sm_not_written 653 8303 (by decide))
    (l16en_w5551_sm_drop 653)
  intro s
  unfold l16enSmRms5552
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8303 5551 5552

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10409 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10409 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16297)
        (denoteGraphDistributedFaithful pm initPM 5551) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1368 l16enPmRms10409
    16297 5551 10409 fw_rms_norm
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1369) (l16en_pm_not_written 1369 10409 (by decide))
    (l16en_nonempty_pm 1368) (l16en_pm_not_written 1368 16297 (by decide))
    (l16en_w5551_pm_drop 1368)
  intro s
  unfold l16enPmRms10409
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16297 5551 10409

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm10410 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10410 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16305)
        (denoteGraphDistributedFaithful pm initPM 5551) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1369 l16enPmRms10410
    16305 5551 10410 fw_rms_norm
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1370) (l16en_pm_not_written 1370 10410 (by decide))
    (l16en_nonempty_pm 1369) (l16en_pm_not_written 1369 16305 (by decide))
    (l16en_w5551_pm_drop 1369)
  intro s
  unfold l16enPmRms10410
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16305 5551 10410

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_sm8314 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8314 =
      denoteGraphDistributedFaithful sm initSM 5552 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 654 l16enSmMulti5
    5552 8314 (fun x => x)
    (by native_decide) l16en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l16en_nonempty_sm 655) (l16en_sm_not_written 655 8314 (by decide))
    (l16en_nonempty_sm 654) (l16en_sm_not_written 654 5552 (by decide))
  intro s
  unfold l16enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l16en_multiref5_first_out sm s 0 5552 8314 8318 8322 8326 8330

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_sm8318 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8318 =
      denoteGraphDistributedFaithful sm initSM 5552 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 654 l16enSmMulti5
    5552 8318 (fun x => x)
    (by native_decide) l16en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l16en_nonempty_sm 655) (l16en_sm_not_written 655 8318 (by decide))
    (l16en_nonempty_sm 654) (l16en_sm_not_written 654 5552 (by decide))
  intro s
  unfold l16enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out sm s 0 5552 8314 8318 8322 8326 8330
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_sm8322 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8322 =
      denoteGraphDistributedFaithful sm initSM 5552 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 654 l16enSmMulti5
    5552 8322 (fun x => x)
    (by native_decide) l16en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l16en_nonempty_sm 655) (l16en_sm_not_written 655 8322 (by decide))
    (l16en_nonempty_sm 654) (l16en_sm_not_written 654 5552 (by decide))
  intro s
  unfold l16enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out sm s 0 5552 8314 8318 8322 8326 8330
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_sm8326 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8326 =
      denoteGraphDistributedFaithful sm initSM 5552 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 654 l16enSmMulti5
    5552 8326 (fun x => x)
    (by native_decide) l16en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l16en_nonempty_sm 655) (l16en_sm_not_written 655 8326 (by decide))
    (l16en_nonempty_sm 654) (l16en_sm_not_written 654 5552 (by decide))
  intro s
  unfold l16enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out sm s 0 5552 8314 8318 8322 8326 8330
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_sm8330 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8330 =
      denoteGraphDistributedFaithful sm initSM 5552 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 654 l16enSmMulti5
    5552 8330 (fun x => x)
    (by native_decide) l16en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l16en_nonempty_sm 655) (l16en_sm_not_written 655 8330 (by decide))
    (l16en_nonempty_sm 654) (l16en_sm_not_written 654 5552 (by decide))
  intro s
  unfold l16enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out sm s 0 5552 8314 8318 8322 8326 8330
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16316 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16316 =
      denoteGraphDistributedFaithful pm initPM 10409 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1370 l16enPmMulti5R0
    10409 16316 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1371) (l16en_pm_not_written 1371 16316 (by decide))
    (l16en_nonempty_pm 1370) (l16en_pm_not_written 1370 10409 (by decide))
  intro s
  unfold l16enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l16en_multiref5_first_out pm s 0 10409 16316 16320 16324 16328 16332

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16320 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16320 =
      denoteGraphDistributedFaithful pm initPM 10409 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1370 l16enPmMulti5R0
    10409 16320 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1371) (l16en_pm_not_written 1371 16320 (by decide))
    (l16en_nonempty_pm 1370) (l16en_pm_not_written 1370 10409 (by decide))
  intro s
  unfold l16enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 0 10409 16316 16320 16324 16328 16332
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16324 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16324 =
      denoteGraphDistributedFaithful pm initPM 10409 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1370 l16enPmMulti5R0
    10409 16324 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1371) (l16en_pm_not_written 1371 16324 (by decide))
    (l16en_nonempty_pm 1370) (l16en_pm_not_written 1370 10409 (by decide))
  intro s
  unfold l16enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 0 10409 16316 16320 16324 16328 16332
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16328 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16328 =
      denoteGraphDistributedFaithful pm initPM 10409 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1370 l16enPmMulti5R0
    10409 16328 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1371) (l16en_pm_not_written 1371 16328 (by decide))
    (l16en_nonempty_pm 1370) (l16en_pm_not_written 1370 10409 (by decide))
  intro s
  unfold l16enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 0 10409 16316 16320 16324 16328 16332
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16332 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16332 =
      denoteGraphDistributedFaithful pm initPM 10409 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1370 l16enPmMulti5R0
    10409 16332 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16en_nonempty_pm 1371) (l16en_pm_not_written 1371 16332 (by decide))
    (l16en_nonempty_pm 1370) (l16en_pm_not_written 1370 10409 (by decide))
  intro s
  unfold l16enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 0 10409 16316 16320 16324 16328 16332
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16339 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16339 =
      denoteGraphDistributedFaithful pm initPM 10410 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1371 l16enPmMulti5R1
    10410 16339 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l16en_nonempty_pm 1372) (l16en_pm_not_written 1372 16339 (by decide))
    (l16en_nonempty_pm 1371) (l16en_pm_not_written 1371 10410 (by decide))
  intro s
  unfold l16enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l16en_multiref5_first_out pm s 1 10410 16339 16343 16347 16351 16355

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16343 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16343 =
      denoteGraphDistributedFaithful pm initPM 10410 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1371 l16enPmMulti5R1
    10410 16343 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l16en_nonempty_pm 1372) (l16en_pm_not_written 1372 16343 (by decide))
    (l16en_nonempty_pm 1371) (l16en_pm_not_written 1371 10410 (by decide))
  intro s
  unfold l16enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 1 10410 16339 16343 16347 16351 16355
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16347 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16347 =
      denoteGraphDistributedFaithful pm initPM 10410 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1371 l16enPmMulti5R1
    10410 16347 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l16en_nonempty_pm 1372) (l16en_pm_not_written 1372 16347 (by decide))
    (l16en_nonempty_pm 1371) (l16en_pm_not_written 1371 10410 (by decide))
  intro s
  unfold l16enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 1 10410 16339 16343 16347 16351 16355
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16351 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16351 =
      denoteGraphDistributedFaithful pm initPM 10410 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1371 l16enPmMulti5R1
    10410 16351 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l16en_nonempty_pm 1372) (l16en_pm_not_written 1372 16351 (by decide))
    (l16en_nonempty_pm 1371) (l16en_pm_not_written 1371 10410 (by decide))
  intro s
  unfold l16enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 1 10410 16339 16343 16347 16351 16355
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16en_red_pm16355 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16355 =
      denoteGraphDistributedFaithful pm initPM 10410 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1371 l16enPmMulti5R1
    10410 16355 (fun x => x)
    (by native_decide) l16en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l16en_nonempty_pm 1372) (l16en_pm_not_written 1372 16355 (by decide))
    (l16en_nonempty_pm 1371) (l16en_pm_not_written 1371 10410 (by decide))
  intro s
  unfold l16enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 1 10410 16339 16343 16347 16351 16355
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5544 (`FW_reshape` of 5543).
theorem recon_zigzagGoal_5544_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5544)
      (denoteGraphDistributedFaithful pm initPM 10377)
      (denoteGraphDistributedFaithful pm initPM 10378)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5543_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16en_red_sm5544 initSM, l16en_red_pm10377 initPM, l16en_red_pm10378 initPM]
  exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hparent (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5545 (`FW_reshape` of 5544).
theorem recon_zigzagGoal_5545_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5545)
      (denoteGraphDistributedFaithful pm initPM 10383)
      (denoteGraphDistributedFaithful pm initPM 10384)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5544_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16en_red_sm5545 initSM, l16en_red_pm10383 initPM, l16en_red_pm10384 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5547 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5547_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5547)
      (denoteGraphDistributedFaithful pm initPM 10387)
      (denoteGraphDistributedFaithful pm initPM 10388)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5545_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5546 = initPM 5546 :=
    recon_weight initSM initPM hInit initGoal_5546 (by native_decide) 5546
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5546 = initSM 5546 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5546
      layer1_sm_nodes_nonempty (fun n hn => (l16en_weights_not_written.1 n hn).1)
  have hpw : denoteGraphDistributedFaithful pm initPM 5546 = initPM 5546 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5546
      layer1_pm_nodes_nonempty (fun n hn => (l16en_weights_not_written.2 n hn).1)
  have hw : denoteGraphDistributedFaithful sm initSM 5546 =
      denoteGraphDistributedFaithful pm initPM 5546 := by
    rw [hsw, hpw]; exact hwInit
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5546).shape =
      [1024, 1024] := by
    rw [hpw]
    exact hPM 5546 [1024, 1024] (by native_decide)
  rw [l16en_red_sm5547 initSM, l16en_red_pm10387 initPM, l16en_red_pm10388 initPM, hw]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5548 (`FW_view` of 5547).
theorem recon_zigzagGoal_5548_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5548)
      (denoteGraphDistributedFaithful pm initPM 10397)
      (denoteGraphDistributedFaithful pm initPM 10398)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5547_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16en_red_sm5548 initSM, l16en_red_pm10397 initPM, l16en_red_pm10398 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5549 (`FW_float` of 5548).
theorem recon_zigzagGoal_5549_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5549)
      (denoteGraphDistributedFaithful pm initPM 10401)
      (denoteGraphDistributedFaithful pm initPM 10402)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5548_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16en_red_sm5549 initSM, l16en_red_pm10401 initPM, l16en_red_pm10402 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5550 (residual `FW_add` of the
-- cross-layer bypass 8299 and 5549).
theorem recon_zigzagGoal_5550_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5550)
      (denoteGraphDistributedFaithful pm initPM 10405)
      (denoteGraphDistributedFaithful pm initPM 10406)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8299_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5549_faithful initSM initPM hSM hPM hInit hValues hCu
  have pmFinal (tid : Tid) (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hw
  have h5492_5541 : denoteGraphDistributedFaithful pm initPM 5492 =
      denoteGraphDistributedFaithful pm initPM 5541 := by
    rw [pmFinal 5492 (fun n hn => (l16en_cu_not_written n hn).1),
      pmFinal 5541 (fun n hn => (l16en_cu_not_written n hn).2)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  rw [h5492_5541] at hA
  rw [l16en_red_sm5550 initSM, l16en_red_pm10405 initPM, l16en_red_pm10406 initPM]
  exact Zigzag2Rel.add 2048 1024 hA hB (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8303 (2-way multiref, position 0).
theorem recon_zigzagGoal_8303_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8303)
      (denoteGraphDistributedFaithful pm initPM 16297)
      (denoteGraphDistributedFaithful pm initPM 16305)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5550_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16en_red_sm8303 initSM, l16en_red_pm16297 initPM, l16en_red_pm16305 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8307 (2-way multiref, position 1).
theorem recon_zigzagGoal_8307_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8307)
      (denoteGraphDistributedFaithful pm initPM 16301)
      (denoteGraphDistributedFaithful pm initPM 16309)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5550_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16en_red_sm8307 initSM, l16en_red_pm16301 initPM, l16en_red_pm16309 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5552 (`FW_rms_norm` of 8303 with
-- the replicated weight 5551).
theorem recon_zigzagGoal_5552_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5552)
      (denoteGraphDistributedFaithful pm initPM 10409)
      (denoteGraphDistributedFaithful pm initPM 10410)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8303_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5551 = initPM 5551 :=
    recon_weight initSM initPM hInit initGoal_5551 (by native_decide) 5551
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5551 = initSM 5551 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5551
      layer1_sm_nodes_nonempty (fun n hn => (l16en_weights_not_written.1 n hn).2)
  have hpw : denoteGraphDistributedFaithful pm initPM 5551 = initPM 5551 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5551
      layer1_pm_nodes_nonempty (fun n hn => (l16en_weights_not_written.2 n hn).2)
  have hw : denoteGraphDistributedFaithful sm initSM 5551 =
      denoteGraphDistributedFaithful pm initPM 5551 := by
    rw [hsw, hpw]; exact hwInit
  rw [l16en_red_sm5552 initSM, l16en_red_pm10409 initPM, l16en_red_pm10410 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8314 (5-way multiref, position 0).
theorem recon_zigzagGoal_8314_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8314)
      (denoteGraphDistributedFaithful pm initPM 16316)
      (denoteGraphDistributedFaithful pm initPM 16339)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5552_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16en_red_sm8314 initSM, l16en_red_pm16316 initPM, l16en_red_pm16339 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8318 (5-way multiref, position 1).
theorem recon_zigzagGoal_8318_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8318)
      (denoteGraphDistributedFaithful pm initPM 16320)
      (denoteGraphDistributedFaithful pm initPM 16343)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5552_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16en_red_sm8318 initSM, l16en_red_pm16320 initPM, l16en_red_pm16343 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8322 (5-way multiref, position 2).
theorem recon_zigzagGoal_8322_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8322)
      (denoteGraphDistributedFaithful pm initPM 16324)
      (denoteGraphDistributedFaithful pm initPM 16347)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5552_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16en_red_sm8322 initSM, l16en_red_pm16324 initPM, l16en_red_pm16347 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8326 (5-way multiref, position 3).
theorem recon_zigzagGoal_8326_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8326)
      (denoteGraphDistributedFaithful pm initPM 16328)
      (denoteGraphDistributedFaithful pm initPM 16351)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5552_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16en_red_sm8326 initSM, l16en_red_pm16328 initPM, l16en_red_pm16351 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8330 (5-way multiref, position 4).
theorem recon_zigzagGoal_8330_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8330)
      (denoteGraphDistributedFaithful pm initPM 16332)
      (denoteGraphDistributedFaithful pm initPM 16355)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5552_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16en_red_sm8330 initSM, l16en_red_pm16332 initPM, l16en_red_pm16355 initPM]
  exact hparent

end
end TrainVerify.Denote.GeneratedPatterns
