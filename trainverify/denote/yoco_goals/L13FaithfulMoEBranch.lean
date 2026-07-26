/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L13FaithfulRouterProj
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-1 MoE branch (router projections + topk / gate / swiglu)

Mechanical transport of the (green) block-0 段 `L12FaithfulRouterProj` +
`L12FaithfulMoEBranch` to block 1.  SM node indices shift by `+35`, PM node
indices by `+70`; every tensor id is re-certified by `native_decide`.

Upper half (router / gate / up projections):

* SM 550 `FW_float [8197] → [5406]`                          (PM 1162 / 1166 → 9895 / 9896)
* SM 551 `FW_reshape [8205] → [5415]`                        (PM 1163 / 1167 → 9915 / 9916)
* SM 552 `FW_reshape [8209] → [5420]`                        (PM 1164 / 1168 → 9929 / 9930)
* SM 553 `FW_reshape [8213] → [5424]`                        (PM 1165 / 1169 → 9947 / 9948)
* SM 554 `FW_norm_linear [5406, 5407] → [5408]`              (PM 1170 / 1174 → 9901 / 9902)
* SM 555 `FW_mix_precision_linear [5415, 5416] → [5417]`     (PM 1171 / 1175 → 9919 / 9920)
* SM 556 `FW_mix_precision_linear [5420, 5421] → [5422]`     (PM 1172 / 1176 → 9933 / 9934)
* SM 557 `FW_mix_precision_linear [5424, 5425] → [5426]`     (PM 1173 / 1177 → 9951 / 9952)

Lower half (topk / views / sigmoid / swiglu):

* SM 558 `FW_topk_routing [5408] → [5409, 5410, 5411]` params `[8, 1]`
    (PM 1178 / 1182 → `9903, 9905, 9907` / `9904, 9906, 9908`)
* SM 559 `FW_view [5417] → [5418]` params `[4096, 1]`        (PM 1179 / 1183 → 9925 / 9926)
* SM 560 `FW_view [5422] → [5423]` params `[4096, 512]`      (PM 1180 / 1184 → 9943 / 9944)
* SM 561 `FW_view [5426] → [5427]` params `[4096, 512]`      (PM 1181 / 1185 → 9961 / 9962)
* SM 563 `FW_sigmoid [5418] → [5419]`                        (PM 1187 / 1190 → 9927 / 9928)
* SM 564 `FW_swiglu [5423, 5427] → [5428]`                   (PM 1188 / 1191 → 9965 / 9966)

Weights 5407 `[64,1024]`, 5416 `[1,1024]`, 5421 `[512,1024]`, 5425 `[512,1024]` are
replicated singletons.  The third `FW_topk_routing` output (`5411`) has no intermediate
goal and is therefore not exported, but the node reduction handles all three outputs.

The `hdec : decodeCuSeqlens cu = [0, 2 * 2048]` side condition of the router lemmas is
**derived** from the ambient `hCu` chain (via the parent relation's `cu_wf` payload plus
the `[2]` shape of the cu tensor 5394).  No new hypotheses are introduced: every theorem
below takes literally the same five parameters as its block-0 counterpart.
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

private def l13mbSmTopk5409 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5408], outs := [5409,5410,5411],
    params := [8,1] }
private def l13mbSmView5418 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5417], outs := [5418], params := [4096,1] }
private def l13mbSmView5423 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5422], outs := [5423], params := [4096,512] }
private def l13mbSmView5427 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5426], outs := [5427], params := [4096,512] }
private def l13mbSmSig5419 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5418], outs := [5419] }
private def l13mbSmSwi5428 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5423,5427], outs := [5428] }

private def l13mbPmTopk9903 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [9901], outs := [9903,9905,9907],
    params := [8,1] }
private def l13mbPmView9925 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9919], outs := [9925], params := [2048,1] }
private def l13mbPmView9943 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9933], outs := [9943], params := [2048,512] }
private def l13mbPmView9961 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9951], outs := [9961], params := [2048,512] }
private def l13mbPmTopk9904 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [9902], outs := [9904,9906,9908],
    params := [8,1] }
private def l13mbPmView9926 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9920], outs := [9926], params := [2048,1] }
private def l13mbPmView9944 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9934], outs := [9944], params := [2048,512] }
private def l13mbPmView9962 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9952], outs := [9962], params := [2048,512] }
private def l13mbPmSig9927 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [9925], outs := [9927] }
private def l13mbPmSwi9965 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [9943,9961], outs := [9965] }
private def l13mbPmSig9928 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [9926], outs := [9928] }
private def l13mbPmSwi9966 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [9944,9962], outs := [9966] }

/-! ### Node literals -/

private theorem l13mb_sm_node_facts :
    sm.nodes[558]'(by native_decide) = l13mbSmTopk5409 ∧
    sm.nodes[559]'(by native_decide) = l13mbSmView5418 ∧
    sm.nodes[560]'(by native_decide) = l13mbSmView5423 ∧
    sm.nodes[561]'(by native_decide) = l13mbSmView5427 ∧
    sm.nodes[563]'(by native_decide) = l13mbSmSig5419 ∧
    sm.nodes[564]'(by native_decide) = l13mbSmSwi5428 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l13mb_pm_node_facts :
    pm.nodes[1178]'(by native_decide) = l13mbPmTopk9903 ∧
    pm.nodes[1179]'(by native_decide) = l13mbPmView9925 ∧
    pm.nodes[1180]'(by native_decide) = l13mbPmView9943 ∧
    pm.nodes[1181]'(by native_decide) = l13mbPmView9961 ∧
    pm.nodes[1182]'(by native_decide) = l13mbPmTopk9904 ∧
    pm.nodes[1183]'(by native_decide) = l13mbPmView9926 ∧
    pm.nodes[1184]'(by native_decide) = l13mbPmView9944 ∧
    pm.nodes[1185]'(by native_decide) = l13mbPmView9962 ∧
    pm.nodes[1187]'(by native_decide) = l13mbPmSig9927 ∧
    pm.nodes[1188]'(by native_decide) = l13mbPmSwi9965 ∧
    pm.nodes[1190]'(by native_decide) = l13mbPmSig9928 ∧
    pm.nodes[1191]'(by native_decide) = l13mbPmSwi9966 := by
  native_decide

private theorem l13mb_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l13mb_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l13mb_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(559, 5409), (559, 5410), (558, 5408), (560, 5418), (559, 5417), (561, 5423), (560, 5422), (562, 5427), (561, 5426), (564, 5419), (563, 5418), (565, 5428), (564, 5423), (564, 5427)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l13mb_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1179, 9903), (1179, 9905), (1178, 9901), (1183, 9904), (1183, 9906), (1182, 9902), (1180, 9925), (1179, 9919), (1181, 9943), (1180, 9933), (1182, 9961), (1181, 9951), (1184, 9926), (1183, 9920), (1185, 9944), (1184, 9934), (1186, 9962), (1185, 9952), (1188, 9927), (1187, 9925), (1191, 9928), (1190, 9926), (1189, 9965), (1188, 9943), (1188, 9961), (1192, 9966), (1191, 9944), (1191, 9962), (1178, 5394)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l13mb_cu_not_written : ∀ n ∈ pm.nodes, 5394 ∉ n.outs := by
  native_decide

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_sm5409 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5408).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5409 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5408) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 558 l13mbSmTopk5409
    5408 5409 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l13mb_sm_node_facts.1 ?_
    (l13mb_nonempty_sm 559) (l13mb_sm_not_written 559 5409 (by decide))
    (l13mb_nonempty_sm 558) (l13mb_sm_not_written 558 5408 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l13mbSmTopk5409
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out sm s 0 5408 5409 5410 5411 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_sm5410 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5408).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5410 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5408) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 558 l13mbSmTopk5409
    5408 5410 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l13mb_sm_node_facts.1 ?_
    (l13mb_nonempty_sm 559) (l13mb_sm_not_written 559 5410 (by decide))
    (l13mb_nonempty_sm 558) (l13mb_sm_not_written 558 5408 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l13mbSmTopk5409
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out sm s 0 5408 5409 5410 5411 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9903 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 9901).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 9903 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 9901) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1178 l13mbPmTopk9903
    9901 9903 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l13mb_pm_node_facts.1 ?_
    (l13mb_nonempty_pm 1179) (l13mb_pm_not_written 1179 9903 (by decide))
    (l13mb_nonempty_pm 1178) (l13mb_pm_not_written 1178 9901 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l13mbPmTopk9903
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 0 9901 9903 9905 9907 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9905 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 9901).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 9905 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 9901) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1178 l13mbPmTopk9903
    9901 9905 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l13mb_pm_node_facts.1 ?_
    (l13mb_nonempty_pm 1179) (l13mb_pm_not_written 1179 9905 (by decide))
    (l13mb_nonempty_pm 1178) (l13mb_pm_not_written 1178 9901 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l13mbPmTopk9903
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 0 9901 9903 9905 9907 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9904 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 9902).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 9904 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 9902) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1182 l13mbPmTopk9904
    9902 9904 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l13mb_pm_node_facts.2.2.2.2.1 ?_
    (l13mb_nonempty_pm 1183) (l13mb_pm_not_written 1183 9904 (by decide))
    (l13mb_nonempty_pm 1182) (l13mb_pm_not_written 1182 9902 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l13mbPmTopk9904
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 1 9902 9904 9906 9908 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9906 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 9902).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 9906 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 9902) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1182 l13mbPmTopk9904
    9902 9906 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l13mb_pm_node_facts.2.2.2.2.1 ?_
    (l13mb_nonempty_pm 1183) (l13mb_pm_not_written 1183 9906 (by decide))
    (l13mb_nonempty_pm 1182) (l13mb_pm_not_written 1182 9902 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l13mbPmTopk9904
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 1 9902 9904 9906 9908 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_sm5418 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5418 =
      fw_view [4096,1] (denoteGraphDistributedFaithful sm initSM 5417) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 559 l13mbSmView5418
    5417 5418 (fun x => fw_view [4096,1] x)
    (by native_decide) l13mb_sm_node_facts.2.1 ?_
    (l13mb_nonempty_sm 560) (l13mb_sm_not_written 560 5418 (by decide))
    (l13mb_nonempty_sm 559) (l13mb_sm_not_written 559 5417 (by decide))
  intro s
  unfold l13mbSmView5418
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1] 5417 5418

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_sm5423 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5423 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5422) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 560 l13mbSmView5423
    5422 5423 (fun x => fw_view [4096,512] x)
    (by native_decide) l13mb_sm_node_facts.2.2.1 ?_
    (l13mb_nonempty_sm 561) (l13mb_sm_not_written 561 5423 (by decide))
    (l13mb_nonempty_sm 560) (l13mb_sm_not_written 560 5422 (by decide))
  intro s
  unfold l13mbSmView5423
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5422 5423

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_sm5427 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5427 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5426) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 561 l13mbSmView5427
    5426 5427 (fun x => fw_view [4096,512] x)
    (by native_decide) l13mb_sm_node_facts.2.2.2.1 ?_
    (l13mb_nonempty_sm 562) (l13mb_sm_not_written 562 5427 (by decide))
    (l13mb_nonempty_sm 561) (l13mb_sm_not_written 561 5426 (by decide))
  intro s
  unfold l13mbSmView5427
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5426 5427

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9925 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9925 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 9919) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1179 l13mbPmView9925
    9919 9925 (fun x => fw_view [2048,1] x)
    (by native_decide) l13mb_pm_node_facts.2.1 ?_
    (l13mb_nonempty_pm 1180) (l13mb_pm_not_written 1180 9925 (by decide))
    (l13mb_nonempty_pm 1179) (l13mb_pm_not_written 1179 9919 (by decide))
  intro s
  unfold l13mbPmView9925
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1] 9919 9925

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9926 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9926 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 9920) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1183 l13mbPmView9926
    9920 9926 (fun x => fw_view [2048,1] x)
    (by native_decide) l13mb_pm_node_facts.2.2.2.2.2.1 ?_
    (l13mb_nonempty_pm 1184) (l13mb_pm_not_written 1184 9926 (by decide))
    (l13mb_nonempty_pm 1183) (l13mb_pm_not_written 1183 9920 (by decide))
  intro s
  unfold l13mbPmView9926
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1] 9920 9926

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9943 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9943 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 9933) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1180 l13mbPmView9943
    9933 9943 (fun x => fw_view [2048,512] x)
    (by native_decide) l13mb_pm_node_facts.2.2.1 ?_
    (l13mb_nonempty_pm 1181) (l13mb_pm_not_written 1181 9943 (by decide))
    (l13mb_nonempty_pm 1180) (l13mb_pm_not_written 1180 9933 (by decide))
  intro s
  unfold l13mbPmView9943
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 9933 9943

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9944 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9944 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 9934) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1184 l13mbPmView9944
    9934 9944 (fun x => fw_view [2048,512] x)
    (by native_decide) l13mb_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l13mb_nonempty_pm 1185) (l13mb_pm_not_written 1185 9944 (by decide))
    (l13mb_nonempty_pm 1184) (l13mb_pm_not_written 1184 9934 (by decide))
  intro s
  unfold l13mbPmView9944
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 9934 9944

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9961 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9961 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 9951) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1181 l13mbPmView9961
    9951 9961 (fun x => fw_view [2048,512] x)
    (by native_decide) l13mb_pm_node_facts.2.2.2.1 ?_
    (l13mb_nonempty_pm 1182) (l13mb_pm_not_written 1182 9961 (by decide))
    (l13mb_nonempty_pm 1181) (l13mb_pm_not_written 1181 9951 (by decide))
  intro s
  unfold l13mbPmView9961
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 9951 9961

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9962 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9962 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 9952) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1185 l13mbPmView9962
    9952 9962 (fun x => fw_view [2048,512] x)
    (by native_decide) l13mb_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l13mb_nonempty_pm 1186) (l13mb_pm_not_written 1186 9962 (by decide))
    (l13mb_nonempty_pm 1185) (l13mb_pm_not_written 1185 9952 (by decide))
  intro s
  unfold l13mbPmView9962
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 9952 9962

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_sm5419 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5419 =
      fw_sigmoid (denoteGraphDistributedFaithful sm initSM 5418) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 563 l13mbSmSig5419
    5418 5419 fw_sigmoid
    (by native_decide) l13mb_sm_node_facts.2.2.2.2.1 ?_
    (l13mb_nonempty_sm 564) (l13mb_sm_not_written 564 5419 (by decide))
    (l13mb_nonempty_sm 563) (l13mb_sm_not_written 563 5418 (by decide))
  intro s
  unfold l13mbSmSig5419
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm s 0 5418 5419

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9927 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9927 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 9925) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1187 l13mbPmSig9927
    9925 9927 fw_sigmoid
    (by native_decide) l13mb_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l13mb_nonempty_pm 1188) (l13mb_pm_not_written 1188 9927 (by decide))
    (l13mb_nonempty_pm 1187) (l13mb_pm_not_written 1187 9925 (by decide))
  intro s
  unfold l13mbPmSig9927
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 0 9925 9927

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9928 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9928 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 9926) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1190 l13mbPmSig9928
    9926 9928 fw_sigmoid
    (by native_decide) l13mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13mb_nonempty_pm 1191) (l13mb_pm_not_written 1191 9928 (by decide))
    (l13mb_nonempty_pm 1190) (l13mb_pm_not_written 1190 9926 (by decide))
  intro s
  unfold l13mbPmSig9928
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 1 9926 9928

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_sm5428 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5428 =
      fw_swiglu (denoteGraphDistributedFaithful sm initSM 5423)
        (denoteGraphDistributedFaithful sm initSM 5427) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 564 l13mbSmSwi5428
    5423 5427 5428 fw_swiglu
    (by native_decide) l13mb_sm_node_facts.2.2.2.2.2 ?_
    (l13mb_nonempty_sm 565) (l13mb_sm_not_written 565 5428 (by decide))
    (l13mb_nonempty_sm 564) (l13mb_sm_not_written 564 5423 (by decide))
    (l13mb_sm_not_written 564 5427 (by decide))
  intro s
  unfold l13mbSmSwi5428
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm s 0 5423 5427 5428

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9965 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9965 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 9943)
        (denoteGraphDistributedFaithful pm initPM 9961) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1188 l13mbPmSwi9965
    9943 9961 9965 fw_swiglu
    (by native_decide) l13mb_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l13mb_nonempty_pm 1189) (l13mb_pm_not_written 1189 9965 (by decide))
    (l13mb_nonempty_pm 1188) (l13mb_pm_not_written 1188 9943 (by decide))
    (l13mb_pm_not_written 1188 9961 (by decide))
  intro s
  unfold l13mbPmSwi9965
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 0 9943 9961 9965

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_red_pm9966 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9966 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 9944)
        (denoteGraphDistributedFaithful pm initPM 9962) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1191 l13mbPmSwi9966
    9944 9962 9966 fw_swiglu
    (by native_decide) l13mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l13mb_nonempty_pm 1192) (l13mb_pm_not_written 1192 9966 (by decide))
    (l13mb_nonempty_pm 1191) (l13mb_pm_not_written 1191 9944 (by decide))
    (l13mb_pm_not_written 1191 9962 (by decide))
  intro s
  unfold l13mbPmSwi9966
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 1 9944 9962 9966

/-! ### `hdec` derived from the ambient zigzag well-formedness -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_cu_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5394).shape = [2] := by
  have e2 : denoteGraphDistributedFaithful pm initPM 5394 = initPM 5394 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5394
      layer1_pm_nodes_nonempty l13mb_cu_not_written
  rw [e2]
  exact hPM 5394 [2] (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13mb_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5394) = [0, 2 * 2048] := by
  have hcuShape := l13mb_cu_shape initPM hPM
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
theorem recon_zigzagGoal_5409_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5409)
      (denoteGraphDistributedFaithful pm initPM 9903)
      (denoteGraphDistributedFaithful pm initPM 9904)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5408_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l13mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5408)
      (denoteGraphDistributedFaithful pm initPM 9901)
      (denoteGraphDistributedFaithful pm initPM 9902)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l13mb_red_sm5409 initSM hs.full_shape,
    l13mb_red_pm9903 initPM hs.rank0_shape,
    l13mb_red_pm9904 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_probs 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5410_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5410)
      (denoteGraphDistributedFaithful pm initPM 9905)
      (denoteGraphDistributedFaithful pm initPM 9906)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5408_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l13mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5408)
      (denoteGraphDistributedFaithful pm initPM 9901)
      (denoteGraphDistributedFaithful pm initPM 9902)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l13mb_red_sm5410 initSM hs.full_shape,
    l13mb_red_pm9905 initPM hs.rank0_shape,
    l13mb_red_pm9906 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_map 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5418_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5418)
      (denoteGraphDistributedFaithful pm initPM 9925)
      (denoteGraphDistributedFaithful pm initPM 9926)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5417_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13mb_red_sm5418 initSM, l13mb_red_pm9925 initPM, l13mb_red_pm9926 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5423_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5423)
      (denoteGraphDistributedFaithful pm initPM 9943)
      (denoteGraphDistributedFaithful pm initPM 9944)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5422_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13mb_red_sm5423 initSM, l13mb_red_pm9943 initPM, l13mb_red_pm9944 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5427_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5427)
      (denoteGraphDistributedFaithful pm initPM 9961)
      (denoteGraphDistributedFaithful pm initPM 9962)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5426_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13mb_red_sm5427 initSM, l13mb_red_pm9961 initPM, l13mb_red_pm9962 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5419_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5419)
      (denoteGraphDistributedFaithful pm initPM 9927)
      (denoteGraphDistributedFaithful pm initPM 9928)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5418_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5418)
      (denoteGraphDistributedFaithful pm initPM 9925)
      (denoteGraphDistributedFaithful pm initPM 9926)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l13mb_red_sm5419 initSM, l13mb_red_pm9927 initPM, l13mb_red_pm9928 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hparent' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5428_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5428)
      (denoteGraphDistributedFaithful pm initPM 9965)
      (denoteGraphDistributedFaithful pm initPM 9966)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 512] [2048, 512] := by
  have hG := recon_zigzagGoal_5423_faithful initSM initPM hSM hPM hInit hValues hCu
  have hU := recon_zigzagGoal_5427_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨g0, g1, hgs⟩ := hG
  obtain ⟨u0, u1, hus⟩ := hU
  have hG' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5423)
      (denoteGraphDistributedFaithful pm initPM 9943)
      (denoteGraphDistributedFaithful pm initPM 9944)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 512] [2048, 512] := ⟨g0, g1, hgs⟩
  have hU' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5427)
      (denoteGraphDistributedFaithful pm initPM 9961)
      (denoteGraphDistributedFaithful pm initPM 9962)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 512] [2048, 512] := ⟨u0, u1, hus⟩
  rw [l13mb_red_sm5428 initSM, l13mb_red_pm9965 initPM, l13mb_red_pm9966 initPM]
  exact Zigzag2Rel.swiglu 2048 512 hG' hU' (by decide) (by decide)

end

end TrainVerify.Denote.GeneratedPatterns
