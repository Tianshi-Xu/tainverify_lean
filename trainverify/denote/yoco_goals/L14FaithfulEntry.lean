/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L14FaithfulZigzagAttention
import denote.yoco_goals.L13FaithfulBlockTail
import denote.yoco_goals.L12FaithfulRouterEntry

/-!
# Faithful zigzag relations for the block-2 entry segment

Continuation of `recon_zigzagGoal_5445_faithful` (block-2 cross-decoder
attention) through the block-2 entry segment:

* SM 576: `FW_reshape [5445] → [5446]`   (PM 1214/1215: `10031 → 10033`, `10032 → 10034`)
* SM 577: `FW_reshape [5446] → [5447]`   (PM 1216/1217: `10033 → 10039`, `10034 → 10040`)
* SM 578: `FW_mix_precision_linear [5447, 5448] → [5449]`
                                          (PM 1218/1219 with replicated weight 5448)
* SM 579: `FW_view [5449] → [5450]`      (PM 1220/1221)
* SM 580: `FW_float [5450] → [5451]`     (PM 1222/1223)
* SM 581: `FW_add [8221, 5451] → [5452]` (PM 1224/1225 with bypass 16129/16137)
* SM 582: `FW_multiref [5452] → [8225, 8229]`
                                          (PM 1226: `[16141, 16145]`, PM 1227: `[16149, 16153]`)
* SM 583: `FW_rms_norm [8225, 5453] → [5454]` (PM 1228/1229, replicated weight 5453)
* SM 584: `FW_multiref [5454] → [8236, 8240, 8244, 8248, 8252]`
                                          (PM 1230: `[16160, 16164, 16168, 16172, 16176]`,
                                           PM 1231: `[16183, 16187, 16191, 16195, 16199]`)

All relations are stated against the block-2 cumulative-sequence metadata tensor
`5443` (the same cu slot used by `recon_zigzagGoal_5445_faithful`).
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

private theorem l14en_multiref5_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 t4 t5 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := [t1, t2, t3, t4, t5], params := [5] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3, t4, t5].zip (List.replicate 5 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ### Node literals -/

private def l14enSmReshape5446 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5445], outs := [5446],
    params := [4096, 1024] }
private def l14enSmReshape5447 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5446], outs := [5447],
    params := [4096, 1024] }
private def l14enSmLinear5449 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5447, 5448],
    outs := [5449] }
private def l14enSmView5450 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5449], outs := [5450],
    params := [4096, 1024] }
private def l14enSmFloat5451 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5450], outs := [5451] }
private def l14enSmAdd5452 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8221, 5451], outs := [5452] }
private def l14enSmMulti2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5452], outs := [8225, 8229],
    params := [2] }
private def l14enSmRms5454 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8225, 5453], outs := [5454] }
private def l14enSmMulti5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5454],
    outs := [8236, 8240, 8244, 8248, 8252], params := [5] }

private def l14enPmReshape10033 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10031], outs := [10033],
    params := [2048, 1024] }
private def l14enPmReshape10034 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10032], outs := [10034],
    params := [2048, 1024] }
private def l14enPmReshape10039 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10033], outs := [10039],
    params := [2048, 1024] }
private def l14enPmReshape10040 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10034], outs := [10040],
    params := [2048, 1024] }
private def l14enPmLinear10043 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10039, 5448],
    outs := [10043] }
private def l14enPmLinear10044 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10040, 5448],
    outs := [10044] }
private def l14enPmView10053 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10043], outs := [10053],
    params := [2048, 1024] }
private def l14enPmView10054 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10044], outs := [10054],
    params := [2048, 1024] }
private def l14enPmFloat10057 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10053], outs := [10057] }
private def l14enPmFloat10058 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10054], outs := [10058] }
private def l14enPmAdd10061 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16129, 10057], outs := [10061] }
private def l14enPmAdd10062 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16137, 10058], outs := [10062] }
private def l14enPmMulti2R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10061], outs := [16141, 16145],
    params := [2] }
private def l14enPmMulti2R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10062], outs := [16149, 16153],
    params := [2] }
private def l14enPmRms10065 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16141, 5453], outs := [10065] }
private def l14enPmRms10066 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16149, 5453], outs := [10066] }
private def l14enPmMulti5R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10065],
    outs := [16160, 16164, 16168, 16172, 16176], params := [5] }
private def l14enPmMulti5R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10066],
    outs := [16183, 16187, 16191, 16195, 16199], params := [5] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l14en_sm_node_facts :
    sm.nodes[576]'(by native_decide) = l14enSmReshape5446 ∧
    sm.nodes[577]'(by native_decide) = l14enSmReshape5447 ∧
    sm.nodes[578]'(by native_decide) = l14enSmLinear5449 ∧
    sm.nodes[579]'(by native_decide) = l14enSmView5450 ∧
    sm.nodes[580]'(by native_decide) = l14enSmFloat5451 ∧
    sm.nodes[581]'(by native_decide) = l14enSmAdd5452 ∧
    sm.nodes[582]'(by native_decide) = l14enSmMulti2 ∧
    sm.nodes[583]'(by native_decide) = l14enSmRms5454 ∧
    sm.nodes[584]'(by native_decide) = l14enSmMulti5 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l14en_pm_node_facts :
    pm.nodes[1214]'(by native_decide) = l14enPmReshape10033 ∧
    pm.nodes[1215]'(by native_decide) = l14enPmReshape10034 ∧
    pm.nodes[1216]'(by native_decide) = l14enPmReshape10039 ∧
    pm.nodes[1217]'(by native_decide) = l14enPmReshape10040 ∧
    pm.nodes[1218]'(by native_decide) = l14enPmLinear10043 ∧
    pm.nodes[1219]'(by native_decide) = l14enPmLinear10044 ∧
    pm.nodes[1220]'(by native_decide) = l14enPmView10053 ∧
    pm.nodes[1221]'(by native_decide) = l14enPmView10054 ∧
    pm.nodes[1222]'(by native_decide) = l14enPmFloat10057 ∧
    pm.nodes[1223]'(by native_decide) = l14enPmFloat10058 ∧
    pm.nodes[1224]'(by native_decide) = l14enPmAdd10061 ∧
    pm.nodes[1225]'(by native_decide) = l14enPmAdd10062 ∧
    pm.nodes[1226]'(by native_decide) = l14enPmMulti2R0 ∧
    pm.nodes[1227]'(by native_decide) = l14enPmMulti2R1 ∧
    pm.nodes[1228]'(by native_decide) = l14enPmRms10065 ∧
    pm.nodes[1229]'(by native_decide) = l14enPmRms10066 ∧
    pm.nodes[1230]'(by native_decide) = l14enPmMulti5R0 ∧
    pm.nodes[1231]'(by native_decide) = l14enPmMulti5R1 := by
  native_decide

private theorem l14en_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l14en_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l14en_weights_not_written :
    (∀ n ∈ sm.nodes, 5448 ∉ n.outs ∧ 5453 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5448 ∉ n.outs ∧ 5453 ∉ n.outs) := by
  native_decide

private theorem l14en_w5448_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5448 ∉ n.outs := by
  intro n hn
  exact (l14en_weights_not_written.1 n (List.mem_of_mem_drop hn)).1

private theorem l14en_w5448_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5448 ∉ n.outs := by
  intro n hn
  exact (l14en_weights_not_written.2 n (List.mem_of_mem_drop hn)).1

private theorem l14en_w5453_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5453 ∉ n.outs := by
  intro n hn
  exact (l14en_weights_not_written.1 n (List.mem_of_mem_drop hn)).2

private theorem l14en_w5453_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5453 ∉ n.outs := by
  intro n hn
  exact (l14en_weights_not_written.2 n (List.mem_of_mem_drop hn)).2

set_option maxRecDepth 1000000 in
private theorem l14en_cu_not_written :
    ∀ n ∈ pm.nodes, 5394 ∉ n.outs ∧ 5443 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l14en_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(577, 5446), (576, 5445), (578, 5447), (579, 5449), (580, 5450), (581,
      5451), (582, 5452), (581, 8221), (583, 8225), (583, 8229), (584, 5454),
      (585, 8236), (585, 8240), (585, 8244), (585, 8248), (585, 8252)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l14en_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1215, 10033), (1214, 10031), (1216, 10034), (1215, 10032), (1217, 10039),
      (1216, 10033), (1218, 10040), (1217, 10034), (1219, 10043), (1218, 10039),
      (1220, 10044), (1219, 10040), (1221, 10053), (1220, 10043), (1222, 10054),
      (1221, 10044), (1223, 10057), (1222, 10053), (1224, 10058), (1223, 10054),
      (1225, 10061), (1224, 16129), (1224, 10057), (1226, 10062), (1225, 16137),
      (1225, 10058), (1227, 16141), (1227, 16145), (1226, 10061), (1228, 16149),
      (1228, 16153), (1227, 10062), (1229, 10065), (1228, 16141), (1230, 10066),
      (1229, 16149), (1231, 16160), (1231, 16164), (1231, 16168), (1231, 16172),
      (1231, 16176), (1230, 10065), (1232, 16183), (1232, 16187), (1232, 16191),
      (1232, 16195), (1232, 16199), (1231, 10066)]) :
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
private theorem l14en_red_sm5446 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5446 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5445) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 576 l14enSmReshape5446
    5445 5446 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l14en_sm_node_facts.1 ?_
    (l14en_nonempty_sm 577) (l14en_sm_not_written 577 5446 (by decide))
    (l14en_nonempty_sm 576) (l14en_sm_not_written 576 5445 (by decide))
  intro s
  unfold l14enSmReshape5446
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5445 5446 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10033 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10033 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10031) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1214 l14enPmReshape10033
    10031 10033 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l14en_pm_node_facts.1 ?_
    (l14en_nonempty_pm 1215) (l14en_pm_not_written 1215 10033 (by decide))
    (l14en_nonempty_pm 1214) (l14en_pm_not_written 1214 10031 (by decide))
  intro s
  unfold l14enPmReshape10033
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10031 10033 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10034 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10034 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10032) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1215 l14enPmReshape10034
    10032 10034 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l14en_pm_node_facts.2.1 ?_
    (l14en_nonempty_pm 1216) (l14en_pm_not_written 1216 10034 (by decide))
    (l14en_nonempty_pm 1215) (l14en_pm_not_written 1215 10032 (by decide))
  intro s
  unfold l14enPmReshape10034
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10032 10034 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_sm5447 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5447 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5446) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 577 l14enSmReshape5447
    5446 5447 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l14en_sm_node_facts.2.1 ?_
    (l14en_nonempty_sm 578) (l14en_sm_not_written 578 5447 (by decide))
    (l14en_nonempty_sm 577) (l14en_sm_not_written 577 5446 (by decide))
  intro s
  unfold l14enSmReshape5447
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5446 5447 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10039 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10039 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10033) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1216 l14enPmReshape10039
    10033 10039 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l14en_pm_node_facts.2.2.1 ?_
    (l14en_nonempty_pm 1217) (l14en_pm_not_written 1217 10039 (by decide))
    (l14en_nonempty_pm 1216) (l14en_pm_not_written 1216 10033 (by decide))
  intro s
  unfold l14enPmReshape10039
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10033 10039 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10040 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10040 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10034) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1217 l14enPmReshape10040
    10034 10040 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l14en_pm_node_facts.2.2.2.1 ?_
    (l14en_nonempty_pm 1218) (l14en_pm_not_written 1218 10040 (by decide))
    (l14en_nonempty_pm 1217) (l14en_pm_not_written 1217 10034 (by decide))
  intro s
  unfold l14enPmReshape10040
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10034 10040 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_sm5449 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5449 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5447)
        (denoteGraphDistributedFaithful sm initSM 5448) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 578 l14enSmLinear5449
    5447 5448 5449 fw_linear
    (by native_decide) l14en_sm_node_facts.2.2.1 ?_
    (l14en_nonempty_sm 579) (l14en_sm_not_written 579 5449 (by decide))
    (l14en_nonempty_sm 578) (l14en_sm_not_written 578 5447 (by decide))
    (l14en_w5448_sm_drop 578)
  intro s
  unfold l14enSmLinear5449
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5447 5448 5449

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10043 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10043 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10039)
        (denoteGraphDistributedFaithful pm initPM 5448) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1218 l14enPmLinear10043
    10039 5448 10043 fw_linear
    (by native_decide) l14en_pm_node_facts.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1219) (l14en_pm_not_written 1219 10043 (by decide))
    (l14en_nonempty_pm 1218) (l14en_pm_not_written 1218 10039 (by decide))
    (l14en_w5448_pm_drop 1218)
  intro s
  unfold l14enPmLinear10043
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10039 5448 10043

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10044 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10044 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10040)
        (denoteGraphDistributedFaithful pm initPM 5448) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1219 l14enPmLinear10044
    10040 5448 10044 fw_linear
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1220) (l14en_pm_not_written 1220 10044 (by decide))
    (l14en_nonempty_pm 1219) (l14en_pm_not_written 1219 10040 (by decide))
    (l14en_w5448_pm_drop 1219)
  intro s
  unfold l14enPmLinear10044
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10040 5448 10044

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_sm5450 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5450 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5449) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 579 l14enSmView5450
    5449 5450 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l14en_sm_node_facts.2.2.2.1 ?_
    (l14en_nonempty_sm 580) (l14en_sm_not_written 580 5450 (by decide))
    (l14en_nonempty_sm 579) (l14en_sm_not_written 579 5449 (by decide))
  intro s
  unfold l14enSmView5450
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5449 5450

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10053 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10053 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10043) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1220 l14enPmView10053
    10043 10053 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1221) (l14en_pm_not_written 1221 10053 (by decide))
    (l14en_nonempty_pm 1220) (l14en_pm_not_written 1220 10043 (by decide))
  intro s
  unfold l14enPmView10053
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 10043 10053

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10054 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10054 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10044) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1221 l14enPmView10054
    10044 10054 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1222) (l14en_pm_not_written 1222 10054 (by decide))
    (l14en_nonempty_pm 1221) (l14en_pm_not_written 1221 10044 (by decide))
  intro s
  unfold l14enPmView10054
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 10044 10054

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_sm5451 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5451 =
      denoteGraphDistributedFaithful sm initSM 5450 := by
  have h := denoteGraphDistributedFaithful_reduce1 sm initSM 580 l14enSmFloat5451
    5450 5451 id
    (by native_decide) l14en_sm_node_facts.2.2.2.2.1 ?_
    (l14en_nonempty_sm 581) (l14en_sm_not_written 581 5451 (by decide))
    (l14en_nonempty_sm 580) (l14en_sm_not_written 580 5450 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l14enSmFloat5451
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out sm s 0 5450 5451 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10057 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10057 =
      denoteGraphDistributedFaithful pm initPM 10053 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1222 l14enPmFloat10057
    10053 10057 id
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1223) (l14en_pm_not_written 1223 10057 (by decide))
    (l14en_nonempty_pm 1222) (l14en_pm_not_written 1222 10053 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l14enPmFloat10057
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 0 10053 10057 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10058 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10058 =
      denoteGraphDistributedFaithful pm initPM 10054 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1223 l14enPmFloat10058
    10054 10058 id
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1224) (l14en_pm_not_written 1224 10058 (by decide))
    (l14en_nonempty_pm 1223) (l14en_pm_not_written 1223 10054 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l14enPmFloat10058
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 1 10054 10058 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_sm5452 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5452 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8221)
        (denoteGraphDistributedFaithful sm initSM 5451) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 581 l14enSmAdd5452
    8221 5451 5452 elemwiseAdd
    (by native_decide) l14en_sm_node_facts.2.2.2.2.2.1 ?_
    (l14en_nonempty_sm 582) (l14en_sm_not_written 582 5452 (by decide))
    (l14en_nonempty_sm 581) (l14en_sm_not_written 581 8221 (by decide))
    (l14en_sm_not_written 581 5451 (by decide))
  intro s
  unfold l14enSmAdd5452
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8221 5451 5452

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10061 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10061 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16129)
        (denoteGraphDistributedFaithful pm initPM 10057) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1224 l14enPmAdd10061
    16129 10057 10061 elemwiseAdd
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1225) (l14en_pm_not_written 1225 10061 (by decide))
    (l14en_nonempty_pm 1224) (l14en_pm_not_written 1224 16129 (by decide))
    (l14en_pm_not_written 1224 10057 (by decide))
  intro s
  unfold l14enPmAdd10061
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16129 10057 10061

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10062 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10062 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16137)
        (denoteGraphDistributedFaithful pm initPM 10058) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1225 l14enPmAdd10062
    16137 10058 10062 elemwiseAdd
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1226) (l14en_pm_not_written 1226 10062 (by decide))
    (l14en_nonempty_pm 1225) (l14en_pm_not_written 1225 16137 (by decide))
    (l14en_pm_not_written 1225 10058 (by decide))
  intro s
  unfold l14enPmAdd10062
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16137 10058 10062

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_sm8225 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8225 =
      denoteGraphDistributedFaithful sm initSM 5452 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 582 l14enSmMulti2
    5452 8225 (fun x => x)
    (by native_decide) l14en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_sm 583) (l14en_sm_not_written 583 8225 (by decide))
    (l14en_nonempty_sm 582) (l14en_sm_not_written 582 5452 (by decide))
  intro s
  unfold l14enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5452 8225 8229

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_sm8229 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8229 =
      denoteGraphDistributedFaithful sm initSM 5452 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 582 l14enSmMulti2
    5452 8229 (fun x => x)
    (by native_decide) l14en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_sm 583) (l14en_sm_not_written 583 8229 (by decide))
    (l14en_nonempty_sm 582) (l14en_sm_not_written 582 5452 (by decide))
  intro s
  unfold l14enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5452 8225 8229 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16141 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16141 =
      denoteGraphDistributedFaithful pm initPM 10061 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1226 l14enPmMulti2R0
    10061 16141 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1227) (l14en_pm_not_written 1227 16141 (by decide))
    (l14en_nonempty_pm 1226) (l14en_pm_not_written 1226 10061 (by decide))
  intro s
  unfold l14enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 10061 16141 16145

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16145 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16145 =
      denoteGraphDistributedFaithful pm initPM 10061 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1226 l14enPmMulti2R0
    10061 16145 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1227) (l14en_pm_not_written 1227 16145 (by decide))
    (l14en_nonempty_pm 1226) (l14en_pm_not_written 1226 10061 (by decide))
  intro s
  unfold l14enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 10061 16141 16145 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16149 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16149 =
      denoteGraphDistributedFaithful pm initPM 10062 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1227 l14enPmMulti2R1
    10062 16149 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1228) (l14en_pm_not_written 1228 16149 (by decide))
    (l14en_nonempty_pm 1227) (l14en_pm_not_written 1227 10062 (by decide))
  intro s
  unfold l14enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 10062 16149 16153

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16153 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16153 =
      denoteGraphDistributedFaithful pm initPM 10062 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1227 l14enPmMulti2R1
    10062 16153 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1228) (l14en_pm_not_written 1228 16153 (by decide))
    (l14en_nonempty_pm 1227) (l14en_pm_not_written 1227 10062 (by decide))
  intro s
  unfold l14enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 10062 16149 16153 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_sm5454 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5454 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8225)
        (denoteGraphDistributedFaithful sm initSM 5453) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 583 l14enSmRms5454
    8225 5453 5454 fw_rms_norm
    (by native_decide) l14en_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_sm 584) (l14en_sm_not_written 584 5454 (by decide))
    (l14en_nonempty_sm 583) (l14en_sm_not_written 583 8225 (by decide))
    (l14en_w5453_sm_drop 583)
  intro s
  unfold l14enSmRms5454
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8225 5453 5454

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10065 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10065 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16141)
        (denoteGraphDistributedFaithful pm initPM 5453) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1228 l14enPmRms10065
    16141 5453 10065 fw_rms_norm
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1229) (l14en_pm_not_written 1229 10065 (by decide))
    (l14en_nonempty_pm 1228) (l14en_pm_not_written 1228 16141 (by decide))
    (l14en_w5453_pm_drop 1228)
  intro s
  unfold l14enPmRms10065
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16141 5453 10065

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm10066 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10066 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16149)
        (denoteGraphDistributedFaithful pm initPM 5453) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1229 l14enPmRms10066
    16149 5453 10066 fw_rms_norm
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1230) (l14en_pm_not_written 1230 10066 (by decide))
    (l14en_nonempty_pm 1229) (l14en_pm_not_written 1229 16149 (by decide))
    (l14en_w5453_pm_drop 1229)
  intro s
  unfold l14enPmRms10066
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16149 5453 10066

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_sm8236 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8236 =
      denoteGraphDistributedFaithful sm initSM 5454 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 584 l14enSmMulti5
    5454 8236 (fun x => x)
    (by native_decide) l14en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l14en_nonempty_sm 585) (l14en_sm_not_written 585 8236 (by decide))
    (l14en_nonempty_sm 584) (l14en_sm_not_written 584 5454 (by decide))
  intro s
  unfold l14enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l14en_multiref5_first_out sm s 0 5454 8236 8240 8244 8248 8252

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_sm8240 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8240 =
      denoteGraphDistributedFaithful sm initSM 5454 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 584 l14enSmMulti5
    5454 8240 (fun x => x)
    (by native_decide) l14en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l14en_nonempty_sm 585) (l14en_sm_not_written 585 8240 (by decide))
    (l14en_nonempty_sm 584) (l14en_sm_not_written 584 5454 (by decide))
  intro s
  unfold l14enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out sm s 0 5454 8236 8240 8244 8248 8252
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_sm8244 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8244 =
      denoteGraphDistributedFaithful sm initSM 5454 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 584 l14enSmMulti5
    5454 8244 (fun x => x)
    (by native_decide) l14en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l14en_nonempty_sm 585) (l14en_sm_not_written 585 8244 (by decide))
    (l14en_nonempty_sm 584) (l14en_sm_not_written 584 5454 (by decide))
  intro s
  unfold l14enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out sm s 0 5454 8236 8240 8244 8248 8252
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_sm8248 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8248 =
      denoteGraphDistributedFaithful sm initSM 5454 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 584 l14enSmMulti5
    5454 8248 (fun x => x)
    (by native_decide) l14en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l14en_nonempty_sm 585) (l14en_sm_not_written 585 8248 (by decide))
    (l14en_nonempty_sm 584) (l14en_sm_not_written 584 5454 (by decide))
  intro s
  unfold l14enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out sm s 0 5454 8236 8240 8244 8248 8252
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_sm8252 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8252 =
      denoteGraphDistributedFaithful sm initSM 5454 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 584 l14enSmMulti5
    5454 8252 (fun x => x)
    (by native_decide) l14en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l14en_nonempty_sm 585) (l14en_sm_not_written 585 8252 (by decide))
    (l14en_nonempty_sm 584) (l14en_sm_not_written 584 5454 (by decide))
  intro s
  unfold l14enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out sm s 0 5454 8236 8240 8244 8248 8252
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16160 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16160 =
      denoteGraphDistributedFaithful pm initPM 10065 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1230 l14enPmMulti5R0
    10065 16160 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1231) (l14en_pm_not_written 1231 16160 (by decide))
    (l14en_nonempty_pm 1230) (l14en_pm_not_written 1230 10065 (by decide))
  intro s
  unfold l14enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l14en_multiref5_first_out pm s 0 10065 16160 16164 16168 16172 16176

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16164 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16164 =
      denoteGraphDistributedFaithful pm initPM 10065 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1230 l14enPmMulti5R0
    10065 16164 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1231) (l14en_pm_not_written 1231 16164 (by decide))
    (l14en_nonempty_pm 1230) (l14en_pm_not_written 1230 10065 (by decide))
  intro s
  unfold l14enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 0 10065 16160 16164 16168 16172 16176
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16168 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16168 =
      denoteGraphDistributedFaithful pm initPM 10065 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1230 l14enPmMulti5R0
    10065 16168 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1231) (l14en_pm_not_written 1231 16168 (by decide))
    (l14en_nonempty_pm 1230) (l14en_pm_not_written 1230 10065 (by decide))
  intro s
  unfold l14enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 0 10065 16160 16164 16168 16172 16176
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16172 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16172 =
      denoteGraphDistributedFaithful pm initPM 10065 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1230 l14enPmMulti5R0
    10065 16172 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1231) (l14en_pm_not_written 1231 16172 (by decide))
    (l14en_nonempty_pm 1230) (l14en_pm_not_written 1230 10065 (by decide))
  intro s
  unfold l14enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 0 10065 16160 16164 16168 16172 16176
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16176 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16176 =
      denoteGraphDistributedFaithful pm initPM 10065 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1230 l14enPmMulti5R0
    10065 16176 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14en_nonempty_pm 1231) (l14en_pm_not_written 1231 16176 (by decide))
    (l14en_nonempty_pm 1230) (l14en_pm_not_written 1230 10065 (by decide))
  intro s
  unfold l14enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 0 10065 16160 16164 16168 16172 16176
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16183 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16183 =
      denoteGraphDistributedFaithful pm initPM 10066 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1231 l14enPmMulti5R1
    10066 16183 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l14en_nonempty_pm 1232) (l14en_pm_not_written 1232 16183 (by decide))
    (l14en_nonempty_pm 1231) (l14en_pm_not_written 1231 10066 (by decide))
  intro s
  unfold l14enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l14en_multiref5_first_out pm s 1 10066 16183 16187 16191 16195 16199

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16187 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16187 =
      denoteGraphDistributedFaithful pm initPM 10066 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1231 l14enPmMulti5R1
    10066 16187 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l14en_nonempty_pm 1232) (l14en_pm_not_written 1232 16187 (by decide))
    (l14en_nonempty_pm 1231) (l14en_pm_not_written 1231 10066 (by decide))
  intro s
  unfold l14enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 1 10066 16183 16187 16191 16195 16199
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16191 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16191 =
      denoteGraphDistributedFaithful pm initPM 10066 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1231 l14enPmMulti5R1
    10066 16191 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l14en_nonempty_pm 1232) (l14en_pm_not_written 1232 16191 (by decide))
    (l14en_nonempty_pm 1231) (l14en_pm_not_written 1231 10066 (by decide))
  intro s
  unfold l14enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 1 10066 16183 16187 16191 16195 16199
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16195 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16195 =
      denoteGraphDistributedFaithful pm initPM 10066 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1231 l14enPmMulti5R1
    10066 16195 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l14en_nonempty_pm 1232) (l14en_pm_not_written 1232 16195 (by decide))
    (l14en_nonempty_pm 1231) (l14en_pm_not_written 1231 10066 (by decide))
  intro s
  unfold l14enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 1 10066 16183 16187 16191 16195 16199
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14en_red_pm16199 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16199 =
      denoteGraphDistributedFaithful pm initPM 10066 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1231 l14enPmMulti5R1
    10066 16199 (fun x => x)
    (by native_decide) l14en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l14en_nonempty_pm 1232) (l14en_pm_not_written 1232 16199 (by decide))
    (l14en_nonempty_pm 1231) (l14en_pm_not_written 1231 10066 (by decide))
  intro s
  unfold l14enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 1 10066 16183 16187 16191 16195 16199
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5446 (`FW_reshape` of 5445).
theorem recon_zigzagGoal_5446_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5446)
      (denoteGraphDistributedFaithful pm initPM 10033)
      (denoteGraphDistributedFaithful pm initPM 10034)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5445_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14en_red_sm5446 initSM, l14en_red_pm10033 initPM, l14en_red_pm10034 initPM]
  exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hparent (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5447 (`FW_reshape` of 5446).
theorem recon_zigzagGoal_5447_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5447)
      (denoteGraphDistributedFaithful pm initPM 10039)
      (denoteGraphDistributedFaithful pm initPM 10040)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5446_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14en_red_sm5447 initSM, l14en_red_pm10039 initPM, l14en_red_pm10040 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5449 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5449_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5449)
      (denoteGraphDistributedFaithful pm initPM 10043)
      (denoteGraphDistributedFaithful pm initPM 10044)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5447_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5448 = initPM 5448 :=
    recon_weight initSM initPM hInit initGoal_5448 (by native_decide) 5448
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5448 = initSM 5448 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5448
      layer1_sm_nodes_nonempty (fun n hn => (l14en_weights_not_written.1 n hn).1)
  have hpw : denoteGraphDistributedFaithful pm initPM 5448 = initPM 5448 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5448
      layer1_pm_nodes_nonempty (fun n hn => (l14en_weights_not_written.2 n hn).1)
  have hw : denoteGraphDistributedFaithful sm initSM 5448 =
      denoteGraphDistributedFaithful pm initPM 5448 := by
    rw [hsw, hpw]; exact hwInit
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5448).shape =
      [1024, 1024] := by
    rw [hpw]
    exact hPM 5448 [1024, 1024] (by native_decide)
  rw [l14en_red_sm5449 initSM, l14en_red_pm10043 initPM, l14en_red_pm10044 initPM, hw]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5450 (`FW_view` of 5449).
theorem recon_zigzagGoal_5450_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5450)
      (denoteGraphDistributedFaithful pm initPM 10053)
      (denoteGraphDistributedFaithful pm initPM 10054)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5449_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14en_red_sm5450 initSM, l14en_red_pm10053 initPM, l14en_red_pm10054 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5451 (`FW_float` of 5450).
theorem recon_zigzagGoal_5451_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5451)
      (denoteGraphDistributedFaithful pm initPM 10057)
      (denoteGraphDistributedFaithful pm initPM 10058)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5450_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14en_red_sm5451 initSM, l14en_red_pm10057 initPM, l14en_red_pm10058 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5452 (residual `FW_add` of the
-- cross-layer bypass 8221 and 5451).
theorem recon_zigzagGoal_5452_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5452)
      (denoteGraphDistributedFaithful pm initPM 10061)
      (denoteGraphDistributedFaithful pm initPM 10062)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8221_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5451_faithful initSM initPM hSM hPM hInit hValues hCu
  have pmFinal (tid : Tid) (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hw
  have h5394_5443 : denoteGraphDistributedFaithful pm initPM 5394 =
      denoteGraphDistributedFaithful pm initPM 5443 := by
    rw [pmFinal 5394 (fun n hn => (l14en_cu_not_written n hn).1),
      pmFinal 5443 (fun n hn => (l14en_cu_not_written n hn).2)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  rw [h5394_5443] at hA
  rw [l14en_red_sm5452 initSM, l14en_red_pm10061 initPM, l14en_red_pm10062 initPM]
  exact Zigzag2Rel.add 2048 1024 hA hB (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8225 (2-way multiref, position 0).
theorem recon_zigzagGoal_8225_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8225)
      (denoteGraphDistributedFaithful pm initPM 16141)
      (denoteGraphDistributedFaithful pm initPM 16149)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5452_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14en_red_sm8225 initSM, l14en_red_pm16141 initPM, l14en_red_pm16149 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8229 (2-way multiref, position 1).
theorem recon_zigzagGoal_8229_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8229)
      (denoteGraphDistributedFaithful pm initPM 16145)
      (denoteGraphDistributedFaithful pm initPM 16153)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5452_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14en_red_sm8229 initSM, l14en_red_pm16145 initPM, l14en_red_pm16153 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5454 (`FW_rms_norm` of 8225 with
-- the replicated weight 5453).
theorem recon_zigzagGoal_5454_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5454)
      (denoteGraphDistributedFaithful pm initPM 10065)
      (denoteGraphDistributedFaithful pm initPM 10066)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8225_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5453 = initPM 5453 :=
    recon_weight initSM initPM hInit initGoal_5453 (by native_decide) 5453
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5453 = initSM 5453 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5453
      layer1_sm_nodes_nonempty (fun n hn => (l14en_weights_not_written.1 n hn).2)
  have hpw : denoteGraphDistributedFaithful pm initPM 5453 = initPM 5453 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5453
      layer1_pm_nodes_nonempty (fun n hn => (l14en_weights_not_written.2 n hn).2)
  have hw : denoteGraphDistributedFaithful sm initSM 5453 =
      denoteGraphDistributedFaithful pm initPM 5453 := by
    rw [hsw, hpw]; exact hwInit
  rw [l14en_red_sm5454 initSM, l14en_red_pm10065 initPM, l14en_red_pm10066 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8236 (5-way multiref, position 0).
theorem recon_zigzagGoal_8236_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8236)
      (denoteGraphDistributedFaithful pm initPM 16160)
      (denoteGraphDistributedFaithful pm initPM 16183)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5454_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14en_red_sm8236 initSM, l14en_red_pm16160 initPM, l14en_red_pm16183 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8240 (5-way multiref, position 1).
theorem recon_zigzagGoal_8240_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8240)
      (denoteGraphDistributedFaithful pm initPM 16164)
      (denoteGraphDistributedFaithful pm initPM 16187)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5454_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14en_red_sm8240 initSM, l14en_red_pm16164 initPM, l14en_red_pm16187 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8244 (5-way multiref, position 2).
theorem recon_zigzagGoal_8244_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8244)
      (denoteGraphDistributedFaithful pm initPM 16168)
      (denoteGraphDistributedFaithful pm initPM 16191)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5454_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14en_red_sm8244 initSM, l14en_red_pm16168 initPM, l14en_red_pm16191 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8248 (5-way multiref, position 3).
theorem recon_zigzagGoal_8248_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8248)
      (denoteGraphDistributedFaithful pm initPM 16172)
      (denoteGraphDistributedFaithful pm initPM 16195)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5454_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14en_red_sm8248 initSM, l14en_red_pm16172 initPM, l14en_red_pm16195 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8252 (5-way multiref, position 4).
theorem recon_zigzagGoal_8252_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8252)
      (denoteGraphDistributedFaithful pm initPM 16176)
      (denoteGraphDistributedFaithful pm initPM 16199)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5454_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14en_red_sm8252 initSM, l14en_red_pm16176 initPM, l14en_red_pm16199 initPM]
  exact hparent

end
end TrainVerify.Denote.GeneratedPatterns
