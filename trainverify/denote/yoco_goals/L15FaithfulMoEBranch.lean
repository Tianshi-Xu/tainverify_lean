/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L15FaithfulRouterProj
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-3 MoE branch (topk / views / sigmoid / swiglu)

Mechanical transport of the (green) block-2 段 `L13FaithfulMoEBranch` to block 3.
The block-3 cu tensor is **5492**.

* SM 628 `FW_topk_routing [5506] → [5507, 5508, 5509]` params `[8, 1]`
    (PM 1318 / 1322 → `10247, 10249, 10251` / `10248, 10250, 10252`)
* SM 629 `FW_view [5515] → [5516]` params `[4096, 1]`        (PM 1319 / 1323 → 10269 / 10270)
* SM 630 `FW_view [5520] → [5521]` params `[4096, 512]`      (PM 1320 / 1324 → 10287 / 10288)
* SM 631 `FW_view [5524] → [5525]` params `[4096, 512]`      (PM 1321 / 1325 → 10305 / 10306)
* SM 633 `FW_sigmoid [5516] → [5517]`                        (PM 1327 / 1330 → 10271 / 10272)
* SM 634 `FW_swiglu [5521, 5525] → [5526]`                   (PM 1328 / 1331 → 10309 / 10310)

The third `FW_topk_routing` output (`5509`) has no intermediate goal and is therefore
not exported, but the node reduction handles all three outputs.
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

private def l15mbSmTopk5507 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5506], outs := [5507,5508,5509],
    params := [8,1] }
private def l15mbSmView5516 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5515], outs := [5516], params := [4096,1] }
private def l15mbSmView5521 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5520], outs := [5521], params := [4096,512] }
private def l15mbSmView5525 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5524], outs := [5525], params := [4096,512] }
private def l15mbSmSig5517 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5516], outs := [5517] }
private def l15mbSmSwi5526 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5521,5525], outs := [5526] }

private def l15mbPmTopk10247 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [10245], outs := [10247,10249,10251],
    params := [8,1] }
private def l15mbPmView10269 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10263], outs := [10269], params := [2048,1] }
private def l15mbPmView10287 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10277], outs := [10287], params := [2048,512] }
private def l15mbPmView10305 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10295], outs := [10305], params := [2048,512] }
private def l15mbPmTopk10248 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [10246], outs := [10248,10250,10252],
    params := [8,1] }
private def l15mbPmView10270 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10264], outs := [10270], params := [2048,1] }
private def l15mbPmView10288 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10278], outs := [10288], params := [2048,512] }
private def l15mbPmView10306 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10296], outs := [10306], params := [2048,512] }
private def l15mbPmSig10271 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [10269], outs := [10271] }
private def l15mbPmSwi10309 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [10287,10305], outs := [10309] }
private def l15mbPmSig10272 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [10270], outs := [10272] }
private def l15mbPmSwi10310 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [10288,10306], outs := [10310] }

/-! ### Certified node indices -/

private theorem l15mb_sm_node_facts :
    sm.nodes[628]'(by native_decide) = l15mbSmTopk5507 ∧
    sm.nodes[629]'(by native_decide) = l15mbSmView5516 ∧
    sm.nodes[630]'(by native_decide) = l15mbSmView5521 ∧
    sm.nodes[631]'(by native_decide) = l15mbSmView5525 ∧
    sm.nodes[633]'(by native_decide) = l15mbSmSig5517 ∧
    sm.nodes[634]'(by native_decide) = l15mbSmSwi5526 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l15mb_pm_node_facts :
    pm.nodes[1318]'(by native_decide) = l15mbPmTopk10247 ∧
    pm.nodes[1319]'(by native_decide) = l15mbPmView10269 ∧
    pm.nodes[1320]'(by native_decide) = l15mbPmView10287 ∧
    pm.nodes[1321]'(by native_decide) = l15mbPmView10305 ∧
    pm.nodes[1322]'(by native_decide) = l15mbPmTopk10248 ∧
    pm.nodes[1323]'(by native_decide) = l15mbPmView10270 ∧
    pm.nodes[1324]'(by native_decide) = l15mbPmView10288 ∧
    pm.nodes[1325]'(by native_decide) = l15mbPmView10306 ∧
    pm.nodes[1327]'(by native_decide) = l15mbPmSig10271 ∧
    pm.nodes[1328]'(by native_decide) = l15mbPmSwi10309 ∧
    pm.nodes[1330]'(by native_decide) = l15mbPmSig10272 ∧
    pm.nodes[1331]'(by native_decide) = l15mbPmSwi10310 := by
  native_decide

private theorem l15mb_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l15mb_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l15mb_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(629, 5507), (629, 5508), (628, 5506), (630, 5516), (629, 5515), (631, 5521), (630, 5520), (632, 5525), (631, 5524), (634, 5517), (633, 5516), (635, 5526), (634, 5521), (634, 5525)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l15mb_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1319, 10247), (1319, 10249), (1318, 10245), (1323, 10248), (1323, 10250), (1322, 10246), (1320, 10269), (1319, 10263), (1321, 10287), (1320, 10277), (1322, 10305), (1321, 10295), (1324, 10270), (1323, 10264), (1325, 10288), (1324, 10278), (1326, 10306), (1325, 10296), (1328, 10271), (1327, 10269), (1331, 10272), (1330, 10270), (1329, 10309), (1328, 10287), (1328, 10305), (1332, 10310), (1331, 10288), (1331, 10306), (1318, 5492)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l15mb_cu_not_written : ∀ n ∈ pm.nodes, 5492 ∉ n.outs := by
  native_decide

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_sm5507 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5506).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5507 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5506) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 628 l15mbSmTopk5507
    5506 5507 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l15mb_sm_node_facts.1 ?_
    (l15mb_nonempty_sm 629) (l15mb_sm_not_written 629 5507 (by decide))
    (l15mb_nonempty_sm 628) (l15mb_sm_not_written 628 5506 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l15mbSmTopk5507
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out sm s 0 5506 5507 5508 5509 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_sm5508 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5506).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5508 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5506) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 628 l15mbSmTopk5507
    5506 5508 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l15mb_sm_node_facts.1 ?_
    (l15mb_nonempty_sm 629) (l15mb_sm_not_written 629 5508 (by decide))
    (l15mb_nonempty_sm 628) (l15mb_sm_not_written 628 5506 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l15mbSmTopk5507
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out sm s 0 5506 5507 5508 5509 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10247 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10245).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10247 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10245) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1318 l15mbPmTopk10247
    10245 10247 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l15mb_pm_node_facts.1 ?_
    (l15mb_nonempty_pm 1319) (l15mb_pm_not_written 1319 10247 (by decide))
    (l15mb_nonempty_pm 1318) (l15mb_pm_not_written 1318 10245 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l15mbPmTopk10247
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 0 10245 10247 10249 10251 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10249 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10245).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10249 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10245) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1318 l15mbPmTopk10247
    10245 10249 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l15mb_pm_node_facts.1 ?_
    (l15mb_nonempty_pm 1319) (l15mb_pm_not_written 1319 10249 (by decide))
    (l15mb_nonempty_pm 1318) (l15mb_pm_not_written 1318 10245 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l15mbPmTopk10247
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 0 10245 10247 10249 10251 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10248 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10246).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10248 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10246) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1322 l15mbPmTopk10248
    10246 10248 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l15mb_pm_node_facts.2.2.2.2.1 ?_
    (l15mb_nonempty_pm 1323) (l15mb_pm_not_written 1323 10248 (by decide))
    (l15mb_nonempty_pm 1322) (l15mb_pm_not_written 1322 10246 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l15mbPmTopk10248
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 1 10246 10248 10250 10252 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10250 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10246).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10250 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10246) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1322 l15mbPmTopk10248
    10246 10250 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l15mb_pm_node_facts.2.2.2.2.1 ?_
    (l15mb_nonempty_pm 1323) (l15mb_pm_not_written 1323 10250 (by decide))
    (l15mb_nonempty_pm 1322) (l15mb_pm_not_written 1322 10246 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l15mbPmTopk10248
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 1 10246 10248 10250 10252 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_sm5516 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5516 =
      fw_view [4096,1] (denoteGraphDistributedFaithful sm initSM 5515) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 629 l15mbSmView5516
    5515 5516 (fun x => fw_view [4096,1] x)
    (by native_decide) l15mb_sm_node_facts.2.1 ?_
    (l15mb_nonempty_sm 630) (l15mb_sm_not_written 630 5516 (by decide))
    (l15mb_nonempty_sm 629) (l15mb_sm_not_written 629 5515 (by decide))
  intro s
  unfold l15mbSmView5516
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1] 5515 5516

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_sm5521 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5521 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5520) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 630 l15mbSmView5521
    5520 5521 (fun x => fw_view [4096,512] x)
    (by native_decide) l15mb_sm_node_facts.2.2.1 ?_
    (l15mb_nonempty_sm 631) (l15mb_sm_not_written 631 5521 (by decide))
    (l15mb_nonempty_sm 630) (l15mb_sm_not_written 630 5520 (by decide))
  intro s
  unfold l15mbSmView5521
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5520 5521

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_sm5525 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5525 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5524) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 631 l15mbSmView5525
    5524 5525 (fun x => fw_view [4096,512] x)
    (by native_decide) l15mb_sm_node_facts.2.2.2.1 ?_
    (l15mb_nonempty_sm 632) (l15mb_sm_not_written 632 5525 (by decide))
    (l15mb_nonempty_sm 631) (l15mb_sm_not_written 631 5524 (by decide))
  intro s
  unfold l15mbSmView5525
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5524 5525

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10269 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10269 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 10263) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1319 l15mbPmView10269
    10263 10269 (fun x => fw_view [2048,1] x)
    (by native_decide) l15mb_pm_node_facts.2.1 ?_
    (l15mb_nonempty_pm 1320) (l15mb_pm_not_written 1320 10269 (by decide))
    (l15mb_nonempty_pm 1319) (l15mb_pm_not_written 1319 10263 (by decide))
  intro s
  unfold l15mbPmView10269
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1] 10263 10269

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10287 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10287 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10277) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1320 l15mbPmView10287
    10277 10287 (fun x => fw_view [2048,512] x)
    (by native_decide) l15mb_pm_node_facts.2.2.1 ?_
    (l15mb_nonempty_pm 1321) (l15mb_pm_not_written 1321 10287 (by decide))
    (l15mb_nonempty_pm 1320) (l15mb_pm_not_written 1320 10277 (by decide))
  intro s
  unfold l15mbPmView10287
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 10277 10287

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10305 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10305 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10295) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1321 l15mbPmView10305
    10295 10305 (fun x => fw_view [2048,512] x)
    (by native_decide) l15mb_pm_node_facts.2.2.2.1 ?_
    (l15mb_nonempty_pm 1322) (l15mb_pm_not_written 1322 10305 (by decide))
    (l15mb_nonempty_pm 1321) (l15mb_pm_not_written 1321 10295 (by decide))
  intro s
  unfold l15mbPmView10305
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 10295 10305

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10270 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10270 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 10264) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1323 l15mbPmView10270
    10264 10270 (fun x => fw_view [2048,1] x)
    (by native_decide) l15mb_pm_node_facts.2.2.2.2.2.1 ?_
    (l15mb_nonempty_pm 1324) (l15mb_pm_not_written 1324 10270 (by decide))
    (l15mb_nonempty_pm 1323) (l15mb_pm_not_written 1323 10264 (by decide))
  intro s
  unfold l15mbPmView10270
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1] 10264 10270

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10288 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10288 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10278) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1324 l15mbPmView10288
    10278 10288 (fun x => fw_view [2048,512] x)
    (by native_decide) l15mb_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l15mb_nonempty_pm 1325) (l15mb_pm_not_written 1325 10288 (by decide))
    (l15mb_nonempty_pm 1324) (l15mb_pm_not_written 1324 10278 (by decide))
  intro s
  unfold l15mbPmView10288
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 10278 10288

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10306 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10306 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10296) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1325 l15mbPmView10306
    10296 10306 (fun x => fw_view [2048,512] x)
    (by native_decide) l15mb_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l15mb_nonempty_pm 1326) (l15mb_pm_not_written 1326 10306 (by decide))
    (l15mb_nonempty_pm 1325) (l15mb_pm_not_written 1325 10296 (by decide))
  intro s
  unfold l15mbPmView10306
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 10296 10306

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_sm5517 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5517 =
      fw_sigmoid (denoteGraphDistributedFaithful sm initSM 5516) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 633 l15mbSmSig5517
    5516 5517 fw_sigmoid
    (by native_decide) l15mb_sm_node_facts.2.2.2.2.1 ?_
    (l15mb_nonempty_sm 634) (l15mb_sm_not_written 634 5517 (by decide))
    (l15mb_nonempty_sm 633) (l15mb_sm_not_written 633 5516 (by decide))
  intro s
  unfold l15mbSmSig5517
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm s 0 5516 5517

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10271 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10271 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 10269) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1327 l15mbPmSig10271
    10269 10271 fw_sigmoid
    (by native_decide) l15mb_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l15mb_nonempty_pm 1328) (l15mb_pm_not_written 1328 10271 (by decide))
    (l15mb_nonempty_pm 1327) (l15mb_pm_not_written 1327 10269 (by decide))
  intro s
  unfold l15mbPmSig10271
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 0 10269 10271

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10272 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10272 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 10270) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1330 l15mbPmSig10272
    10270 10272 fw_sigmoid
    (by native_decide) l15mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15mb_nonempty_pm 1331) (l15mb_pm_not_written 1331 10272 (by decide))
    (l15mb_nonempty_pm 1330) (l15mb_pm_not_written 1330 10270 (by decide))
  intro s
  unfold l15mbPmSig10272
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 1 10270 10272

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_sm5526 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5526 =
      fw_swiglu (denoteGraphDistributedFaithful sm initSM 5521)
        (denoteGraphDistributedFaithful sm initSM 5525) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 634 l15mbSmSwi5526
    5521 5525 5526 fw_swiglu
    (by native_decide) l15mb_sm_node_facts.2.2.2.2.2 ?_
    (l15mb_nonempty_sm 635) (l15mb_sm_not_written 635 5526 (by decide))
    (l15mb_nonempty_sm 634) (l15mb_sm_not_written 634 5521 (by decide))
    (l15mb_sm_not_written 634 5525 (by decide))
  intro s
  unfold l15mbSmSwi5526
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm s 0 5521 5525 5526

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10309 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10309 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 10287)
        (denoteGraphDistributedFaithful pm initPM 10305) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1328 l15mbPmSwi10309
    10287 10305 10309 fw_swiglu
    (by native_decide) l15mb_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l15mb_nonempty_pm 1329) (l15mb_pm_not_written 1329 10309 (by decide))
    (l15mb_nonempty_pm 1328) (l15mb_pm_not_written 1328 10287 (by decide))
    (l15mb_pm_not_written 1328 10305 (by decide))
  intro s
  unfold l15mbPmSwi10309
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 0 10287 10305 10309

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_red_pm10310 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10310 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 10288)
        (denoteGraphDistributedFaithful pm initPM 10306) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1331 l15mbPmSwi10310
    10288 10306 10310 fw_swiglu
    (by native_decide) l15mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l15mb_nonempty_pm 1332) (l15mb_pm_not_written 1332 10310 (by decide))
    (l15mb_nonempty_pm 1331) (l15mb_pm_not_written 1331 10288 (by decide))
    (l15mb_pm_not_written 1331 10306 (by decide))
  intro s
  unfold l15mbPmSwi10310
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 1 10288 10306 10310

/-! ### `hdec` derived from the ambient zigzag well-formedness -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_cu_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5492).shape = [2] := by
  have e2 : denoteGraphDistributedFaithful pm initPM 5492 = initPM 5492 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5492
      layer1_pm_nodes_nonempty l15mb_cu_not_written
  rw [e2]
  exact hPM 5492 [2] (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15mb_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5492) = [0, 2 * 2048] := by
  have hcuShape := l15mb_cu_shape initPM hPM
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
theorem recon_zigzagGoal_5507_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5507)
      (denoteGraphDistributedFaithful pm initPM 10247)
      (denoteGraphDistributedFaithful pm initPM 10248)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5506_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l15mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5506)
      (denoteGraphDistributedFaithful pm initPM 10245)
      (denoteGraphDistributedFaithful pm initPM 10246)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l15mb_red_sm5507 initSM hs.full_shape,
    l15mb_red_pm10247 initPM hs.rank0_shape,
    l15mb_red_pm10248 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_probs 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5508_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5508)
      (denoteGraphDistributedFaithful pm initPM 10249)
      (denoteGraphDistributedFaithful pm initPM 10250)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5506_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l15mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5506)
      (denoteGraphDistributedFaithful pm initPM 10245)
      (denoteGraphDistributedFaithful pm initPM 10246)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l15mb_red_sm5508 initSM hs.full_shape,
    l15mb_red_pm10249 initPM hs.rank0_shape,
    l15mb_red_pm10250 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_map 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5516_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5516)
      (denoteGraphDistributedFaithful pm initPM 10269)
      (denoteGraphDistributedFaithful pm initPM 10270)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5515_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15mb_red_sm5516 initSM, l15mb_red_pm10269 initPM, l15mb_red_pm10270 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5521_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5521)
      (denoteGraphDistributedFaithful pm initPM 10287)
      (denoteGraphDistributedFaithful pm initPM 10288)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5520_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15mb_red_sm5521 initSM, l15mb_red_pm10287 initPM, l15mb_red_pm10288 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5525_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5525)
      (denoteGraphDistributedFaithful pm initPM 10305)
      (denoteGraphDistributedFaithful pm initPM 10306)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5524_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15mb_red_sm5525 initSM, l15mb_red_pm10305 initPM, l15mb_red_pm10306 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5517_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5517)
      (denoteGraphDistributedFaithful pm initPM 10271)
      (denoteGraphDistributedFaithful pm initPM 10272)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5516_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5516)
      (denoteGraphDistributedFaithful pm initPM 10269)
      (denoteGraphDistributedFaithful pm initPM 10270)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l15mb_red_sm5517 initSM, l15mb_red_pm10271 initPM, l15mb_red_pm10272 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hparent' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5526_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5526)
      (denoteGraphDistributedFaithful pm initPM 10309)
      (denoteGraphDistributedFaithful pm initPM 10310)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 512] [2048, 512] := by
  have hG := recon_zigzagGoal_5521_faithful initSM initPM hSM hPM hInit hValues hCu
  have hU := recon_zigzagGoal_5525_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨g0, g1, hgs⟩ := hG
  obtain ⟨u0, u1, hus⟩ := hU
  have hG' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5521)
      (denoteGraphDistributedFaithful pm initPM 10287)
      (denoteGraphDistributedFaithful pm initPM 10288)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 512] [2048, 512] := ⟨g0, g1, hgs⟩
  have hU' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5525)
      (denoteGraphDistributedFaithful pm initPM 10305)
      (denoteGraphDistributedFaithful pm initPM 10306)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 512] [2048, 512] := ⟨u0, u1, hus⟩
  rw [l15mb_red_sm5526 initSM, l15mb_red_pm10309 initPM, l15mb_red_pm10310 initPM]
  exact Zigzag2Rel.swiglu 2048 512 hG' hU' (by decide) (by decide)

end

end TrainVerify.Denote.GeneratedPatterns
