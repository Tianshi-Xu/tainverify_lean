/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L12FaithfulViewChain
import denote.yoco_goals.ZigzagPointwiseRel
import denote.yoco_goals.ZigzagLinearRel

/-!
# Faithful zigzag relation for generated goals 5349 / 5351 / 5352

Continuation of `recon_zigzagGoal_5348_faithful` three steps down the generated
graph:

* SM node 507: `FW_reshape [5348] → [5349]`, params `[4096, 1024]`
  (PM 1076/1077: `[9689] → [9695]`, `[9690] → [9696]`, params `[2048, 1024]`)
* SM node 508: `FW_mix_precision_linear [5349, 5350] → [5351]`
  (PM 1078/1079: `[9695, 5350] → [9699]`, `[9696, 5350] → [9700]`)
* SM node 509: `FW_view [5351] → [5352]`, params `[4096, 1024]`
  (PM 1080/1081: `[9699] → [9709]`, `[9700] → [9710]`, params `[2048, 1024]`)

Tensor 5350 is a replicated `[1024, 1024]` weight (`initGoal_5350`).

Both reshape/view steps are shape-identity, hence handled by
`Zigzag2Rel.view_id'`; the linear step is handled by
`Zigzag2Rel.mix_precision_linear` (`FW_mix_precision_linear` dispatches to
`fw_linear` in `evalOp`).
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

private def l12SmReshape5349 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5348], outs := [5349],
    params := [4096, 1024] }
private def l12PmReshape9695 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9689], outs := [9695],
    params := [2048, 1024] }
private def l12PmReshape9696 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9690], outs := [9696],
    params := [2048, 1024] }

private def l12SmLinear5351 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5349, 5350],
    outs := [5351] }
private def l12PmLinear9699 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9695, 5350],
    outs := [9699] }
private def l12PmLinear9700 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9696, 5350],
    outs := [9700] }

private def l12SmView5352 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5351], outs := [5352],
    params := [4096, 1024] }
private def l12PmView9709 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9699], outs := [9709],
    params := [2048, 1024] }
private def l12PmView9710 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9700], outs := [9710],
    params := [2048, 1024] }

set_option maxRecDepth 1000000 in
private theorem l12lin_sm_node_facts :
    sm.nodes[507]'(by native_decide) = l12SmReshape5349 ∧
    sm.nodes[508]'(by native_decide) = l12SmLinear5351 ∧
    sm.nodes[509]'(by native_decide) = l12SmView5352 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12lin_pm_node_facts :
    pm.nodes[1076]'(by native_decide) = l12PmReshape9695 ∧
    pm.nodes[1077]'(by native_decide) = l12PmReshape9696 ∧
    pm.nodes[1078]'(by native_decide) = l12PmLinear9699 ∧
    pm.nodes[1079]'(by native_decide) = l12PmLinear9700 ∧
    pm.nodes[1080]'(by native_decide) = l12PmView9709 ∧
    pm.nodes[1081]'(by native_decide) = l12PmView9710 := by
  native_decide

private theorem l12lin_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l12lin_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12lin_weight5350_not_written :
    (∀ n ∈ sm.nodes, 5350 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5350 ∉ n.outs) := by
  native_decide

private theorem l12lin_w5350_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5350 ∉ n.outs := by
  intro n hn
  exact l12lin_weight5350_not_written.1 n (List.mem_of_mem_drop hn)

private theorem l12lin_w5350_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5350 ∉ n.outs := by
  intro n hn
  exact l12lin_weight5350_not_written.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12lin_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(508, 5349), (507, 5348), (509, 5351), (508, 5349),
      (510, 5352), (509, 5351)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12lin_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1077, 9695), (1078, 9696), (1076, 9689), (1077, 9690),
      (1079, 9699), (1080, 9700), (1078, 9695), (1079, 9696),
      (1081, 9709), (1082, 9710), (1080, 9699), (1081, 9700)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12lin_red_sm5349 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5349 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5348) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 507 l12SmReshape5349
    5348 5349 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l12lin_sm_node_facts.1 ?_
    (l12lin_nonempty_sm 508) (l12lin_sm_not_written 508 5349 (by decide))
    (l12lin_nonempty_sm 507) (l12lin_sm_not_written 507 5348 (by decide))
  intro s
  unfold l12SmReshape5349
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5348 5349 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12lin_red_pm9695 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9695 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9689) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1076 l12PmReshape9695
    9689 9695 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l12lin_pm_node_facts.1 ?_
    (l12lin_nonempty_pm 1077) (l12lin_pm_not_written 1077 9695 (by decide))
    (l12lin_nonempty_pm 1076) (l12lin_pm_not_written 1076 9689 (by decide))
  intro s
  unfold l12PmReshape9695
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 9689 9695 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12lin_red_pm9696 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9696 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9690) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1077 l12PmReshape9696
    9690 9696 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l12lin_pm_node_facts.2.1 ?_
    (l12lin_nonempty_pm 1078) (l12lin_pm_not_written 1078 9696 (by decide))
    (l12lin_nonempty_pm 1077) (l12lin_pm_not_written 1077 9690 (by decide))
  intro s
  unfold l12PmReshape9696
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 9690 9696 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12lin_red_sm5351 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5351 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5349)
        (denoteGraphDistributedFaithful sm initSM 5350) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 508 l12SmLinear5351
    5349 5350 5351 fw_linear
    (by native_decide) l12lin_sm_node_facts.2.1 ?_
    (l12lin_nonempty_sm 509) (l12lin_sm_not_written 509 5351 (by decide))
    (l12lin_nonempty_sm 508) (l12lin_sm_not_written 508 5349 (by decide))
    (l12lin_w5350_sm_drop 508)
  intro s
  unfold l12SmLinear5351
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5349 5350 5351

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12lin_red_pm9699 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9699 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9695)
        (denoteGraphDistributedFaithful pm initPM 5350) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1078 l12PmLinear9699
    9695 5350 9699 fw_linear
    (by native_decide) l12lin_pm_node_facts.2.2.1 ?_
    (l12lin_nonempty_pm 1079) (l12lin_pm_not_written 1079 9699 (by decide))
    (l12lin_nonempty_pm 1078) (l12lin_pm_not_written 1078 9695 (by decide))
    (l12lin_w5350_pm_drop 1078)
  intro s
  unfold l12PmLinear9699
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 9695 5350 9699

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12lin_red_pm9700 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9700 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9696)
        (denoteGraphDistributedFaithful pm initPM 5350) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1079 l12PmLinear9700
    9696 5350 9700 fw_linear
    (by native_decide) l12lin_pm_node_facts.2.2.2.1 ?_
    (l12lin_nonempty_pm 1080) (l12lin_pm_not_written 1080 9700 (by decide))
    (l12lin_nonempty_pm 1079) (l12lin_pm_not_written 1079 9696 (by decide))
    (l12lin_w5350_pm_drop 1079)
  intro s
  unfold l12PmLinear9700
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 9696 5350 9700

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12lin_red_sm5352 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5352 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5351) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 509 l12SmView5352
    5351 5352 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l12lin_sm_node_facts.2.2 ?_
    (l12lin_nonempty_sm 510) (l12lin_sm_not_written 510 5352 (by decide))
    (l12lin_nonempty_sm 509) (l12lin_sm_not_written 509 5351 (by decide))
  intro s
  unfold l12SmView5352
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5351 5352

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12lin_red_pm9709 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9709 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9699) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1080 l12PmView9709
    9699 9709 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l12lin_pm_node_facts.2.2.2.2.1 ?_
    (l12lin_nonempty_pm 1081) (l12lin_pm_not_written 1081 9709 (by decide))
    (l12lin_nonempty_pm 1080) (l12lin_pm_not_written 1080 9699 (by decide))
  intro s
  unfold l12PmView9709
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 9699 9709

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12lin_red_pm9710 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9710 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9700) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1081 l12PmView9710
    9700 9710 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l12lin_pm_node_facts.2.2.2.2.2 ?_
    (l12lin_nonempty_pm 1082) (l12lin_pm_not_written 1082 9710 (by decide))
    (l12lin_nonempty_pm 1081) (l12lin_pm_not_written 1081 9700 (by decide))
  intro s
  unfold l12PmView9710
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 9700 9710

/-! ### Goals -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5349 (`FW_reshape` of 5348).
theorem recon_zigzagGoal_5349_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5349)
      (denoteGraphDistributedFaithful pm initPM 9695)
      (denoteGraphDistributedFaithful pm initPM 9696)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5348_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12lin_red_sm5349 initSM, l12lin_red_pm9695 initPM, l12lin_red_pm9696 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5351 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5351_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5351)
      (denoteGraphDistributedFaithful pm initPM 9699)
      (denoteGraphDistributedFaithful pm initPM 9700)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5349_faithful initSM initPM hSM hPM hInit hValues hCu
  -- the replicated weight 5350 agrees on both sides
  have hwInit : initSM 5350 = initPM 5350 :=
    recon_weight initSM initPM hInit initGoal_5350 (by native_decide) 5350
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5350 = initSM 5350 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5350
      layer1_sm_nodes_nonempty l12lin_weight5350_not_written.1
  have hpw : denoteGraphDistributedFaithful pm initPM 5350 = initPM 5350 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5350
      layer1_pm_nodes_nonempty l12lin_weight5350_not_written.2
  have hw : denoteGraphDistributedFaithful sm initSM 5350 =
      denoteGraphDistributedFaithful pm initPM 5350 := by
    rw [hsw, hpw]; exact hwInit
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5350).shape =
      [1024, 1024] := by
    rw [hpw]
    exact hPM 5350 [1024, 1024] (by native_decide)
  rw [l12lin_red_sm5351 initSM, l12lin_red_pm9699 initPM, l12lin_red_pm9700 initPM, hw]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5352 (`FW_view` of 5351).
theorem recon_zigzagGoal_5352_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5352)
      (denoteGraphDistributedFaithful pm initPM 9709)
      (denoteGraphDistributedFaithful pm initPM 9710)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5351_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12lin_red_sm5352 initSM, l12lin_red_pm9709 initPM, l12lin_red_pm9710 initPM]
  exact Zigzag2Rel.view_id' hparent

end
end TrainVerify.Denote.GeneratedPatterns
