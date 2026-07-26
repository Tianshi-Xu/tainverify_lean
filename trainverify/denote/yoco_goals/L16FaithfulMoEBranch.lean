/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L16FaithfulRouterProj
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-4 MoE branch (topk / views / sigmoid / swiglu)

Mechanical transport of the (green) block-3 段 `L13FaithfulMoEBranch` to block 4.
The block-4 cu tensor is **5541**.

* SM 663 `FW_topk_routing [5555] → [5556, 5557, 5558]` params `[8, 1]`
    (PM 1388 / 1392 → `10419, 10421, 10423` / `10420, 10422, 10424`)
* SM 664 `FW_view [5564] → [5565]` params `[4096, 1]`        (PM 1389 / 1393 → 10441 / 10442)
* SM 665 `FW_view [5569] → [5570]` params `[4096, 512]`      (PM 1390 / 1394 → 10459 / 10460)
* SM 666 `FW_view [5573] → [5574]` params `[4096, 512]`      (PM 1391 / 1395 → 10477 / 10478)
* SM 668 `FW_sigmoid [5565] → [5566]`                        (PM 1397 / 1400 → 10443 / 10444)
* SM 669 `FW_swiglu [5570, 5574] → [5575]`                   (PM 1398 / 1401 → 10481 / 10482)

The third `FW_topk_routing` output (`5558`) has no intermediate goal and is therefore
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

private def l16mbSmTopk5556 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5555], outs := [5556,5557,5558],
    params := [8,1] }
private def l16mbSmView5565 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5564], outs := [5565], params := [4096,1] }
private def l16mbSmView5570 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5569], outs := [5570], params := [4096,512] }
private def l16mbSmView5574 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5573], outs := [5574], params := [4096,512] }
private def l16mbSmSig5566 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5565], outs := [5566] }
private def l16mbSmSwi5575 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5570,5574], outs := [5575] }

private def l16mbPmTopk10419 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [10417], outs := [10419,10421,10423],
    params := [8,1] }
private def l16mbPmView10441 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10435], outs := [10441], params := [2048,1] }
private def l16mbPmView10459 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10449], outs := [10459], params := [2048,512] }
private def l16mbPmView10477 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10467], outs := [10477], params := [2048,512] }
private def l16mbPmTopk10420 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [10418], outs := [10420,10422,10424],
    params := [8,1] }
private def l16mbPmView10442 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10436], outs := [10442], params := [2048,1] }
private def l16mbPmView10460 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10450], outs := [10460], params := [2048,512] }
private def l16mbPmView10478 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10468], outs := [10478], params := [2048,512] }
private def l16mbPmSig10443 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [10441], outs := [10443] }
private def l16mbPmSwi10481 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [10459,10477], outs := [10481] }
private def l16mbPmSig10444 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [10442], outs := [10444] }
private def l16mbPmSwi10482 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [10460,10478], outs := [10482] }

/-! ### Certified node indices -/

private theorem l16mb_sm_node_facts :
    sm.nodes[663]'(by native_decide) = l16mbSmTopk5556 ∧
    sm.nodes[664]'(by native_decide) = l16mbSmView5565 ∧
    sm.nodes[665]'(by native_decide) = l16mbSmView5570 ∧
    sm.nodes[666]'(by native_decide) = l16mbSmView5574 ∧
    sm.nodes[668]'(by native_decide) = l16mbSmSig5566 ∧
    sm.nodes[669]'(by native_decide) = l16mbSmSwi5575 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l16mb_pm_node_facts :
    pm.nodes[1388]'(by native_decide) = l16mbPmTopk10419 ∧
    pm.nodes[1389]'(by native_decide) = l16mbPmView10441 ∧
    pm.nodes[1390]'(by native_decide) = l16mbPmView10459 ∧
    pm.nodes[1391]'(by native_decide) = l16mbPmView10477 ∧
    pm.nodes[1392]'(by native_decide) = l16mbPmTopk10420 ∧
    pm.nodes[1393]'(by native_decide) = l16mbPmView10442 ∧
    pm.nodes[1394]'(by native_decide) = l16mbPmView10460 ∧
    pm.nodes[1395]'(by native_decide) = l16mbPmView10478 ∧
    pm.nodes[1397]'(by native_decide) = l16mbPmSig10443 ∧
    pm.nodes[1398]'(by native_decide) = l16mbPmSwi10481 ∧
    pm.nodes[1400]'(by native_decide) = l16mbPmSig10444 ∧
    pm.nodes[1401]'(by native_decide) = l16mbPmSwi10482 := by
  native_decide

private theorem l16mb_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l16mb_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l16mb_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(664, 5556), (664, 5557), (663, 5555), (665, 5565), (664, 5564), (666, 5570), (665, 5569), (667, 5574), (666, 5573), (669, 5566), (668, 5565), (670, 5575), (669, 5570), (669, 5574)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l16mb_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1389, 10419), (1389, 10421), (1388, 10417), (1393, 10420), (1393, 10422), (1392, 10418), (1390, 10441), (1389, 10435), (1391, 10459), (1390, 10449), (1392, 10477), (1391, 10467), (1394, 10442), (1393, 10436), (1395, 10460), (1394, 10450), (1396, 10478), (1395, 10468), (1398, 10443), (1397, 10441), (1401, 10444), (1400, 10442), (1399, 10481), (1398, 10459), (1398, 10477), (1402, 10482), (1401, 10460), (1401, 10478), (1388, 5541)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l16mb_cu_not_written : ∀ n ∈ pm.nodes, 5541 ∉ n.outs := by
  native_decide

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_sm5556 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5555).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5556 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5555) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 663 l16mbSmTopk5556
    5555 5556 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l16mb_sm_node_facts.1 ?_
    (l16mb_nonempty_sm 664) (l16mb_sm_not_written 664 5556 (by decide))
    (l16mb_nonempty_sm 663) (l16mb_sm_not_written 663 5555 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l16mbSmTopk5556
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out sm s 0 5555 5556 5557 5558 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_sm5557 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5555).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5557 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5555) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 663 l16mbSmTopk5556
    5555 5557 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l16mb_sm_node_facts.1 ?_
    (l16mb_nonempty_sm 664) (l16mb_sm_not_written 664 5557 (by decide))
    (l16mb_nonempty_sm 663) (l16mb_sm_not_written 663 5555 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l16mbSmTopk5556
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out sm s 0 5555 5556 5557 5558 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10419 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10417).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10419 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10417) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1388 l16mbPmTopk10419
    10417 10419 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l16mb_pm_node_facts.1 ?_
    (l16mb_nonempty_pm 1389) (l16mb_pm_not_written 1389 10419 (by decide))
    (l16mb_nonempty_pm 1388) (l16mb_pm_not_written 1388 10417 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l16mbPmTopk10419
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 0 10417 10419 10421 10423 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10421 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10417).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10421 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10417) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1388 l16mbPmTopk10419
    10417 10421 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l16mb_pm_node_facts.1 ?_
    (l16mb_nonempty_pm 1389) (l16mb_pm_not_written 1389 10421 (by decide))
    (l16mb_nonempty_pm 1388) (l16mb_pm_not_written 1388 10417 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l16mbPmTopk10419
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 0 10417 10419 10421 10423 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10420 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10418).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10420 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10418) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1392 l16mbPmTopk10420
    10418 10420 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l16mb_pm_node_facts.2.2.2.2.1 ?_
    (l16mb_nonempty_pm 1393) (l16mb_pm_not_written 1393 10420 (by decide))
    (l16mb_nonempty_pm 1392) (l16mb_pm_not_written 1392 10418 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l16mbPmTopk10420
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 1 10418 10420 10422 10424 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10422 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10418).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10422 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10418) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1392 l16mbPmTopk10420
    10418 10422 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l16mb_pm_node_facts.2.2.2.2.1 ?_
    (l16mb_nonempty_pm 1393) (l16mb_pm_not_written 1393 10422 (by decide))
    (l16mb_nonempty_pm 1392) (l16mb_pm_not_written 1392 10418 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l16mbPmTopk10420
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 1 10418 10420 10422 10424 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_sm5565 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5565 =
      fw_view [4096,1] (denoteGraphDistributedFaithful sm initSM 5564) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 664 l16mbSmView5565
    5564 5565 (fun x => fw_view [4096,1] x)
    (by native_decide) l16mb_sm_node_facts.2.1 ?_
    (l16mb_nonempty_sm 665) (l16mb_sm_not_written 665 5565 (by decide))
    (l16mb_nonempty_sm 664) (l16mb_sm_not_written 664 5564 (by decide))
  intro s
  unfold l16mbSmView5565
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1] 5564 5565

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_sm5570 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5570 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5569) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 665 l16mbSmView5570
    5569 5570 (fun x => fw_view [4096,512] x)
    (by native_decide) l16mb_sm_node_facts.2.2.1 ?_
    (l16mb_nonempty_sm 666) (l16mb_sm_not_written 666 5570 (by decide))
    (l16mb_nonempty_sm 665) (l16mb_sm_not_written 665 5569 (by decide))
  intro s
  unfold l16mbSmView5570
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5569 5570

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_sm5574 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5574 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5573) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 666 l16mbSmView5574
    5573 5574 (fun x => fw_view [4096,512] x)
    (by native_decide) l16mb_sm_node_facts.2.2.2.1 ?_
    (l16mb_nonempty_sm 667) (l16mb_sm_not_written 667 5574 (by decide))
    (l16mb_nonempty_sm 666) (l16mb_sm_not_written 666 5573 (by decide))
  intro s
  unfold l16mbSmView5574
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5573 5574

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10441 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10441 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 10435) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1389 l16mbPmView10441
    10435 10441 (fun x => fw_view [2048,1] x)
    (by native_decide) l16mb_pm_node_facts.2.1 ?_
    (l16mb_nonempty_pm 1390) (l16mb_pm_not_written 1390 10441 (by decide))
    (l16mb_nonempty_pm 1389) (l16mb_pm_not_written 1389 10435 (by decide))
  intro s
  unfold l16mbPmView10441
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1] 10435 10441

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10459 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10459 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10449) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1390 l16mbPmView10459
    10449 10459 (fun x => fw_view [2048,512] x)
    (by native_decide) l16mb_pm_node_facts.2.2.1 ?_
    (l16mb_nonempty_pm 1391) (l16mb_pm_not_written 1391 10459 (by decide))
    (l16mb_nonempty_pm 1390) (l16mb_pm_not_written 1390 10449 (by decide))
  intro s
  unfold l16mbPmView10459
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 10449 10459

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10477 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10477 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10467) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1391 l16mbPmView10477
    10467 10477 (fun x => fw_view [2048,512] x)
    (by native_decide) l16mb_pm_node_facts.2.2.2.1 ?_
    (l16mb_nonempty_pm 1392) (l16mb_pm_not_written 1392 10477 (by decide))
    (l16mb_nonempty_pm 1391) (l16mb_pm_not_written 1391 10467 (by decide))
  intro s
  unfold l16mbPmView10477
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 10467 10477

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10442 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10442 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 10436) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1393 l16mbPmView10442
    10436 10442 (fun x => fw_view [2048,1] x)
    (by native_decide) l16mb_pm_node_facts.2.2.2.2.2.1 ?_
    (l16mb_nonempty_pm 1394) (l16mb_pm_not_written 1394 10442 (by decide))
    (l16mb_nonempty_pm 1393) (l16mb_pm_not_written 1393 10436 (by decide))
  intro s
  unfold l16mbPmView10442
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1] 10436 10442

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10460 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10460 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10450) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1394 l16mbPmView10460
    10450 10460 (fun x => fw_view [2048,512] x)
    (by native_decide) l16mb_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l16mb_nonempty_pm 1395) (l16mb_pm_not_written 1395 10460 (by decide))
    (l16mb_nonempty_pm 1394) (l16mb_pm_not_written 1394 10450 (by decide))
  intro s
  unfold l16mbPmView10460
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 10450 10460

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10478 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10478 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10468) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1395 l16mbPmView10478
    10468 10478 (fun x => fw_view [2048,512] x)
    (by native_decide) l16mb_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l16mb_nonempty_pm 1396) (l16mb_pm_not_written 1396 10478 (by decide))
    (l16mb_nonempty_pm 1395) (l16mb_pm_not_written 1395 10468 (by decide))
  intro s
  unfold l16mbPmView10478
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 10468 10478

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_sm5566 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5566 =
      fw_sigmoid (denoteGraphDistributedFaithful sm initSM 5565) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 668 l16mbSmSig5566
    5565 5566 fw_sigmoid
    (by native_decide) l16mb_sm_node_facts.2.2.2.2.1 ?_
    (l16mb_nonempty_sm 669) (l16mb_sm_not_written 669 5566 (by decide))
    (l16mb_nonempty_sm 668) (l16mb_sm_not_written 668 5565 (by decide))
  intro s
  unfold l16mbSmSig5566
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm s 0 5565 5566

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10443 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10443 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 10441) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1397 l16mbPmSig10443
    10441 10443 fw_sigmoid
    (by native_decide) l16mb_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l16mb_nonempty_pm 1398) (l16mb_pm_not_written 1398 10443 (by decide))
    (l16mb_nonempty_pm 1397) (l16mb_pm_not_written 1397 10441 (by decide))
  intro s
  unfold l16mbPmSig10443
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 0 10441 10443

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10444 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10444 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 10442) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1400 l16mbPmSig10444
    10442 10444 fw_sigmoid
    (by native_decide) l16mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16mb_nonempty_pm 1401) (l16mb_pm_not_written 1401 10444 (by decide))
    (l16mb_nonempty_pm 1400) (l16mb_pm_not_written 1400 10442 (by decide))
  intro s
  unfold l16mbPmSig10444
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 1 10442 10444

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_sm5575 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5575 =
      fw_swiglu (denoteGraphDistributedFaithful sm initSM 5570)
        (denoteGraphDistributedFaithful sm initSM 5574) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 669 l16mbSmSwi5575
    5570 5574 5575 fw_swiglu
    (by native_decide) l16mb_sm_node_facts.2.2.2.2.2 ?_
    (l16mb_nonempty_sm 670) (l16mb_sm_not_written 670 5575 (by decide))
    (l16mb_nonempty_sm 669) (l16mb_sm_not_written 669 5570 (by decide))
    (l16mb_sm_not_written 669 5574 (by decide))
  intro s
  unfold l16mbSmSwi5575
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm s 0 5570 5574 5575

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10481 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10481 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 10459)
        (denoteGraphDistributedFaithful pm initPM 10477) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1398 l16mbPmSwi10481
    10459 10477 10481 fw_swiglu
    (by native_decide) l16mb_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l16mb_nonempty_pm 1399) (l16mb_pm_not_written 1399 10481 (by decide))
    (l16mb_nonempty_pm 1398) (l16mb_pm_not_written 1398 10459 (by decide))
    (l16mb_pm_not_written 1398 10477 (by decide))
  intro s
  unfold l16mbPmSwi10481
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 0 10459 10477 10481

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_red_pm10482 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10482 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 10460)
        (denoteGraphDistributedFaithful pm initPM 10478) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1401 l16mbPmSwi10482
    10460 10478 10482 fw_swiglu
    (by native_decide) l16mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l16mb_nonempty_pm 1402) (l16mb_pm_not_written 1402 10482 (by decide))
    (l16mb_nonempty_pm 1401) (l16mb_pm_not_written 1401 10460 (by decide))
    (l16mb_pm_not_written 1401 10478 (by decide))
  intro s
  unfold l16mbPmSwi10482
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 1 10460 10478 10482

/-! ### `hdec` derived from the ambient zigzag well-formedness -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_cu_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5541).shape = [2] := by
  have e2 : denoteGraphDistributedFaithful pm initPM 5541 = initPM 5541 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5541
      layer1_pm_nodes_nonempty l16mb_cu_not_written
  rw [e2]
  exact hPM 5541 [2] (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16mb_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5541) = [0, 2 * 2048] := by
  have hcuShape := l16mb_cu_shape initPM hPM
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5541)).length = 2 := by
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
theorem recon_zigzagGoal_5556_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5556)
      (denoteGraphDistributedFaithful pm initPM 10419)
      (denoteGraphDistributedFaithful pm initPM 10420)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5555_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l16mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5555)
      (denoteGraphDistributedFaithful pm initPM 10417)
      (denoteGraphDistributedFaithful pm initPM 10418)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l16mb_red_sm5556 initSM hs.full_shape,
    l16mb_red_pm10419 initPM hs.rank0_shape,
    l16mb_red_pm10420 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_probs 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5557_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5557)
      (denoteGraphDistributedFaithful pm initPM 10421)
      (denoteGraphDistributedFaithful pm initPM 10422)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5555_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l16mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5555)
      (denoteGraphDistributedFaithful pm initPM 10417)
      (denoteGraphDistributedFaithful pm initPM 10418)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l16mb_red_sm5557 initSM hs.full_shape,
    l16mb_red_pm10421 initPM hs.rank0_shape,
    l16mb_red_pm10422 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_map 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5565_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5565)
      (denoteGraphDistributedFaithful pm initPM 10441)
      (denoteGraphDistributedFaithful pm initPM 10442)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5564_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16mb_red_sm5565 initSM, l16mb_red_pm10441 initPM, l16mb_red_pm10442 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5570_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5570)
      (denoteGraphDistributedFaithful pm initPM 10459)
      (denoteGraphDistributedFaithful pm initPM 10460)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5569_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16mb_red_sm5570 initSM, l16mb_red_pm10459 initPM, l16mb_red_pm10460 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5574_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5574)
      (denoteGraphDistributedFaithful pm initPM 10477)
      (denoteGraphDistributedFaithful pm initPM 10478)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5573_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16mb_red_sm5574 initSM, l16mb_red_pm10477 initPM, l16mb_red_pm10478 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5566_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5566)
      (denoteGraphDistributedFaithful pm initPM 10443)
      (denoteGraphDistributedFaithful pm initPM 10444)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5565_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5565)
      (denoteGraphDistributedFaithful pm initPM 10441)
      (denoteGraphDistributedFaithful pm initPM 10442)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l16mb_red_sm5566 initSM, l16mb_red_pm10443 initPM, l16mb_red_pm10444 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hparent' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5575_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5575)
      (denoteGraphDistributedFaithful pm initPM 10481)
      (denoteGraphDistributedFaithful pm initPM 10482)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 512] [2048, 512] := by
  have hG := recon_zigzagGoal_5570_faithful initSM initPM hSM hPM hInit hValues hCu
  have hU := recon_zigzagGoal_5574_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨g0, g1, hgs⟩ := hG
  obtain ⟨u0, u1, hus⟩ := hU
  have hG' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5570)
      (denoteGraphDistributedFaithful pm initPM 10459)
      (denoteGraphDistributedFaithful pm initPM 10460)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 512] [2048, 512] := ⟨g0, g1, hgs⟩
  have hU' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5574)
      (denoteGraphDistributedFaithful pm initPM 10477)
      (denoteGraphDistributedFaithful pm initPM 10478)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 512] [2048, 512] := ⟨u0, u1, hus⟩
  rw [l16mb_red_sm5575 initSM, l16mb_red_pm10481 initPM, l16mb_red_pm10482 initPM]
  exact Zigzag2Rel.swiglu 2048 512 hG' hU' (by decide) (by decide)

end

end TrainVerify.Denote.GeneratedPatterns
