/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L19FaithfulZigzagAttention
import denote.yoco_goals.L18FaithfulBlockTail
import denote.yoco_goals.L12FaithfulRouterEntry

/-!
# Faithful zigzag relations for the block-7 entry segment

Continuation of `recon_zigzagGoal_5690_faithful` (block-7 cross-decoder
attention) through the block-7 entry segment:

* SM 751: `FW_reshape [5690] → [5691]`   (PM 1564/1565: `10891 → 10893`, `10892 → 10894`)
* SM 752: `FW_reshape [5691] → [5692]`   (PM 1566/1567: `10893 → 10899`, `10894 → 10900`)
* SM 753: `FW_mix_precision_linear [5692, 5693] → [5694]`
                                          (PM 1568/1569 with replicated weight 5693)
* SM 754: `FW_view [5694] → [5695]`      (PM 1570/1571)
* SM 755: `FW_float [5695] → [5696]`     (PM 1572/1573)
* SM 756: `FW_add [8416, 5696] → [5697]` (PM 1574/1575 with bypass 16519/16527)
* SM 757: `FW_multiref [5697] → [8420, 8424]`
                                          (PM 1576: `[16531, 16535]`, PM 1577: `[16539, 16543]`)
* SM 758: `FW_rms_norm [8420, 5698] → [5699]` (PM 1578/1579, replicated weight 5698)
* SM 759: `FW_multiref [5699] → [8431, 8435, 8439, 8443, 8447]`
                                          (PM 1580: `[16550, 16554, 16558, 16562, 16566]`,
                                           PM 1581: `[16573, 16577, 16581, 16585, 16589]`)

All relations are stated against the block-7 cumulative-sequence metadata tensor
`5688` (the same cu slot used by `recon_zigzagGoal_5690_faithful`).
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

private theorem l19en_multiref5_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 t4 t5 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := [t1, t2, t3, t4, t5], params := [5] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3, t4, t5].zip (List.replicate 5 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ### Node literals -/

private def l19enSmReshape5691 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5690], outs := [5691],
    params := [4096, 1024] }
private def l19enSmReshape5692 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5691], outs := [5692],
    params := [4096, 1024] }
private def l19enSmLinear5694 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5692, 5693],
    outs := [5694] }
private def l19enSmView5695 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5694], outs := [5695],
    params := [4096, 1024] }
private def l19enSmFloat5696 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5695], outs := [5696] }
private def l19enSmAdd5697 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8416, 5696], outs := [5697] }
private def l19enSmMulti2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5697], outs := [8420, 8424],
    params := [2] }
private def l19enSmRms5699 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8420, 5698], outs := [5699] }
private def l19enSmMulti5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5699],
    outs := [8431, 8435, 8439, 8443, 8447], params := [5] }

private def l19enPmReshape10893 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10891], outs := [10893],
    params := [2048, 1024] }
private def l19enPmReshape10894 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10892], outs := [10894],
    params := [2048, 1024] }
private def l19enPmReshape10899 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10893], outs := [10899],
    params := [2048, 1024] }
private def l19enPmReshape10900 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10894], outs := [10900],
    params := [2048, 1024] }
private def l19enPmLinear10903 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10899, 5693],
    outs := [10903] }
private def l19enPmLinear10904 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10900, 5693],
    outs := [10904] }
private def l19enPmView10913 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10903], outs := [10913],
    params := [2048, 1024] }
private def l19enPmView10914 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10904], outs := [10914],
    params := [2048, 1024] }
private def l19enPmFloat10917 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10913], outs := [10917] }
private def l19enPmFloat10918 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10914], outs := [10918] }
private def l19enPmAdd10921 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16519, 10917], outs := [10921] }
private def l19enPmAdd10922 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16527, 10918], outs := [10922] }
private def l19enPmMulti2R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10921], outs := [16531, 16535],
    params := [2] }
private def l19enPmMulti2R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10922], outs := [16539, 16543],
    params := [2] }
private def l19enPmRms10925 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16531, 5698], outs := [10925] }
private def l19enPmRms10926 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16539, 5698], outs := [10926] }
private def l19enPmMulti5R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10925],
    outs := [16550, 16554, 16558, 16562, 16566], params := [5] }
private def l19enPmMulti5R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10926],
    outs := [16573, 16577, 16581, 16585, 16589], params := [5] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l19en_sm_node_facts :
    sm.nodes[751]'(by native_decide) = l19enSmReshape5691 ∧
    sm.nodes[752]'(by native_decide) = l19enSmReshape5692 ∧
    sm.nodes[753]'(by native_decide) = l19enSmLinear5694 ∧
    sm.nodes[754]'(by native_decide) = l19enSmView5695 ∧
    sm.nodes[755]'(by native_decide) = l19enSmFloat5696 ∧
    sm.nodes[756]'(by native_decide) = l19enSmAdd5697 ∧
    sm.nodes[757]'(by native_decide) = l19enSmMulti2 ∧
    sm.nodes[758]'(by native_decide) = l19enSmRms5699 ∧
    sm.nodes[759]'(by native_decide) = l19enSmMulti5 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l19en_pm_node_facts :
    pm.nodes[1564]'(by native_decide) = l19enPmReshape10893 ∧
    pm.nodes[1565]'(by native_decide) = l19enPmReshape10894 ∧
    pm.nodes[1566]'(by native_decide) = l19enPmReshape10899 ∧
    pm.nodes[1567]'(by native_decide) = l19enPmReshape10900 ∧
    pm.nodes[1568]'(by native_decide) = l19enPmLinear10903 ∧
    pm.nodes[1569]'(by native_decide) = l19enPmLinear10904 ∧
    pm.nodes[1570]'(by native_decide) = l19enPmView10913 ∧
    pm.nodes[1571]'(by native_decide) = l19enPmView10914 ∧
    pm.nodes[1572]'(by native_decide) = l19enPmFloat10917 ∧
    pm.nodes[1573]'(by native_decide) = l19enPmFloat10918 ∧
    pm.nodes[1574]'(by native_decide) = l19enPmAdd10921 ∧
    pm.nodes[1575]'(by native_decide) = l19enPmAdd10922 ∧
    pm.nodes[1576]'(by native_decide) = l19enPmMulti2R0 ∧
    pm.nodes[1577]'(by native_decide) = l19enPmMulti2R1 ∧
    pm.nodes[1578]'(by native_decide) = l19enPmRms10925 ∧
    pm.nodes[1579]'(by native_decide) = l19enPmRms10926 ∧
    pm.nodes[1580]'(by native_decide) = l19enPmMulti5R0 ∧
    pm.nodes[1581]'(by native_decide) = l19enPmMulti5R1 := by
  native_decide

private theorem l19en_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l19en_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l19en_weights_not_written :
    (∀ n ∈ sm.nodes, 5693 ∉ n.outs ∧ 5698 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5693 ∉ n.outs ∧ 5698 ∉ n.outs) := by
  native_decide

private theorem l19en_w5693_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5693 ∉ n.outs := by
  intro n hn
  exact (l19en_weights_not_written.1 n (List.mem_of_mem_drop hn)).1

private theorem l19en_w5693_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5693 ∉ n.outs := by
  intro n hn
  exact (l19en_weights_not_written.2 n (List.mem_of_mem_drop hn)).1

private theorem l19en_w5698_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5698 ∉ n.outs := by
  intro n hn
  exact (l19en_weights_not_written.1 n (List.mem_of_mem_drop hn)).2

private theorem l19en_w5698_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5698 ∉ n.outs := by
  intro n hn
  exact (l19en_weights_not_written.2 n (List.mem_of_mem_drop hn)).2

set_option maxRecDepth 1000000 in
private theorem l19en_cu_not_written :
    ∀ n ∈ pm.nodes, 5639 ∉ n.outs ∧ 5688 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l19en_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(752, 5691), (751, 5690), (753, 5692), (754, 5694), (755, 5695), (756,
      5696), (757, 5697), (756, 8416), (758, 8420), (758, 8424), (759, 5699),
      (760, 8431), (760, 8435), (760, 8439), (760, 8443), (760, 8447)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l19en_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1565, 10893), (1564, 10891), (1566, 10894), (1565, 10892), (1567, 10899),
      (1566, 10893), (1568, 10900), (1567, 10894), (1569, 10903), (1568, 10899),
      (1570, 10904), (1569, 10900), (1571, 10913), (1570, 10903), (1572, 10914),
      (1571, 10904), (1573, 10917), (1572, 10913), (1574, 10918), (1573, 10914),
      (1575, 10921), (1574, 16519), (1574, 10917), (1576, 10922), (1575, 16527),
      (1575, 10918), (1577, 16531), (1577, 16535), (1576, 10921), (1578, 16539),
      (1578, 16543), (1577, 10922), (1579, 10925), (1578, 16531), (1580, 10926),
      (1579, 16539), (1581, 16550), (1581, 16554), (1581, 16558), (1581, 16562),
      (1581, 16566), (1580, 10925), (1582, 16573), (1582, 16577), (1582, 16581),
      (1582, 16585), (1582, 16589), (1581, 10926)]) :
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
private theorem l19en_red_sm5691 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5691 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5690) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 751 l19enSmReshape5691
    5690 5691 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l19en_sm_node_facts.1 ?_
    (l19en_nonempty_sm 752) (l19en_sm_not_written 752 5691 (by decide))
    (l19en_nonempty_sm 751) (l19en_sm_not_written 751 5690 (by decide))
  intro s
  unfold l19enSmReshape5691
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5690 5691 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10893 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10893 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10891) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1564 l19enPmReshape10893
    10891 10893 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l19en_pm_node_facts.1 ?_
    (l19en_nonempty_pm 1565) (l19en_pm_not_written 1565 10893 (by decide))
    (l19en_nonempty_pm 1564) (l19en_pm_not_written 1564 10891 (by decide))
  intro s
  unfold l19enPmReshape10893
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10891 10893 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10894 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10894 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10892) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1565 l19enPmReshape10894
    10892 10894 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l19en_pm_node_facts.2.1 ?_
    (l19en_nonempty_pm 1566) (l19en_pm_not_written 1566 10894 (by decide))
    (l19en_nonempty_pm 1565) (l19en_pm_not_written 1565 10892 (by decide))
  intro s
  unfold l19enPmReshape10894
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10892 10894 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_sm5692 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5692 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5691) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 752 l19enSmReshape5692
    5691 5692 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l19en_sm_node_facts.2.1 ?_
    (l19en_nonempty_sm 753) (l19en_sm_not_written 753 5692 (by decide))
    (l19en_nonempty_sm 752) (l19en_sm_not_written 752 5691 (by decide))
  intro s
  unfold l19enSmReshape5692
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5691 5692 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10899 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10899 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10893) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1566 l19enPmReshape10899
    10893 10899 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l19en_pm_node_facts.2.2.1 ?_
    (l19en_nonempty_pm 1567) (l19en_pm_not_written 1567 10899 (by decide))
    (l19en_nonempty_pm 1566) (l19en_pm_not_written 1566 10893 (by decide))
  intro s
  unfold l19enPmReshape10899
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10893 10899 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10900 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10900 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10894) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1567 l19enPmReshape10900
    10894 10900 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l19en_pm_node_facts.2.2.2.1 ?_
    (l19en_nonempty_pm 1568) (l19en_pm_not_written 1568 10900 (by decide))
    (l19en_nonempty_pm 1567) (l19en_pm_not_written 1567 10894 (by decide))
  intro s
  unfold l19enPmReshape10900
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10894 10900 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_sm5694 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5694 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5692)
        (denoteGraphDistributedFaithful sm initSM 5693) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 753 l19enSmLinear5694
    5692 5693 5694 fw_linear
    (by native_decide) l19en_sm_node_facts.2.2.1 ?_
    (l19en_nonempty_sm 754) (l19en_sm_not_written 754 5694 (by decide))
    (l19en_nonempty_sm 753) (l19en_sm_not_written 753 5692 (by decide))
    (l19en_w5693_sm_drop 753)
  intro s
  unfold l19enSmLinear5694
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5692 5693 5694

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10903 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10903 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10899)
        (denoteGraphDistributedFaithful pm initPM 5693) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1568 l19enPmLinear10903
    10899 5693 10903 fw_linear
    (by native_decide) l19en_pm_node_facts.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1569) (l19en_pm_not_written 1569 10903 (by decide))
    (l19en_nonempty_pm 1568) (l19en_pm_not_written 1568 10899 (by decide))
    (l19en_w5693_pm_drop 1568)
  intro s
  unfold l19enPmLinear10903
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10899 5693 10903

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10904 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10904 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10900)
        (denoteGraphDistributedFaithful pm initPM 5693) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1569 l19enPmLinear10904
    10900 5693 10904 fw_linear
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1570) (l19en_pm_not_written 1570 10904 (by decide))
    (l19en_nonempty_pm 1569) (l19en_pm_not_written 1569 10900 (by decide))
    (l19en_w5693_pm_drop 1569)
  intro s
  unfold l19enPmLinear10904
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10900 5693 10904

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_sm5695 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5695 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5694) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 754 l19enSmView5695
    5694 5695 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l19en_sm_node_facts.2.2.2.1 ?_
    (l19en_nonempty_sm 755) (l19en_sm_not_written 755 5695 (by decide))
    (l19en_nonempty_sm 754) (l19en_sm_not_written 754 5694 (by decide))
  intro s
  unfold l19enSmView5695
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5694 5695

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10913 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10913 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10903) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1570 l19enPmView10913
    10903 10913 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1571) (l19en_pm_not_written 1571 10913 (by decide))
    (l19en_nonempty_pm 1570) (l19en_pm_not_written 1570 10903 (by decide))
  intro s
  unfold l19enPmView10913
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 10903 10913

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10914 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10914 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10904) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1571 l19enPmView10914
    10904 10914 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1572) (l19en_pm_not_written 1572 10914 (by decide))
    (l19en_nonempty_pm 1571) (l19en_pm_not_written 1571 10904 (by decide))
  intro s
  unfold l19enPmView10914
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 10904 10914

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_sm5696 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5696 =
      denoteGraphDistributedFaithful sm initSM 5695 := by
  have h := denoteGraphDistributedFaithful_reduce1 sm initSM 755 l19enSmFloat5696
    5695 5696 id
    (by native_decide) l19en_sm_node_facts.2.2.2.2.1 ?_
    (l19en_nonempty_sm 756) (l19en_sm_not_written 756 5696 (by decide))
    (l19en_nonempty_sm 755) (l19en_sm_not_written 755 5695 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l19enSmFloat5696
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out sm s 0 5695 5696 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10917 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10917 =
      denoteGraphDistributedFaithful pm initPM 10913 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1572 l19enPmFloat10917
    10913 10917 id
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1573) (l19en_pm_not_written 1573 10917 (by decide))
    (l19en_nonempty_pm 1572) (l19en_pm_not_written 1572 10913 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l19enPmFloat10917
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 0 10913 10917 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10918 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10918 =
      denoteGraphDistributedFaithful pm initPM 10914 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1573 l19enPmFloat10918
    10914 10918 id
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1574) (l19en_pm_not_written 1574 10918 (by decide))
    (l19en_nonempty_pm 1573) (l19en_pm_not_written 1573 10914 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l19enPmFloat10918
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 1 10914 10918 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_sm5697 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5697 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8416)
        (denoteGraphDistributedFaithful sm initSM 5696) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 756 l19enSmAdd5697
    8416 5696 5697 elemwiseAdd
    (by native_decide) l19en_sm_node_facts.2.2.2.2.2.1 ?_
    (l19en_nonempty_sm 757) (l19en_sm_not_written 757 5697 (by decide))
    (l19en_nonempty_sm 756) (l19en_sm_not_written 756 8416 (by decide))
    (l19en_sm_not_written 756 5696 (by decide))
  intro s
  unfold l19enSmAdd5697
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8416 5696 5697

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10921 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10921 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16519)
        (denoteGraphDistributedFaithful pm initPM 10917) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1574 l19enPmAdd10921
    16519 10917 10921 elemwiseAdd
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1575) (l19en_pm_not_written 1575 10921 (by decide))
    (l19en_nonempty_pm 1574) (l19en_pm_not_written 1574 16519 (by decide))
    (l19en_pm_not_written 1574 10917 (by decide))
  intro s
  unfold l19enPmAdd10921
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16519 10917 10921

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10922 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10922 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16527)
        (denoteGraphDistributedFaithful pm initPM 10918) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1575 l19enPmAdd10922
    16527 10918 10922 elemwiseAdd
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1576) (l19en_pm_not_written 1576 10922 (by decide))
    (l19en_nonempty_pm 1575) (l19en_pm_not_written 1575 16527 (by decide))
    (l19en_pm_not_written 1575 10918 (by decide))
  intro s
  unfold l19enPmAdd10922
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16527 10918 10922

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_sm8420 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8420 =
      denoteGraphDistributedFaithful sm initSM 5697 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 757 l19enSmMulti2
    5697 8420 (fun x => x)
    (by native_decide) l19en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_sm 758) (l19en_sm_not_written 758 8420 (by decide))
    (l19en_nonempty_sm 757) (l19en_sm_not_written 757 5697 (by decide))
  intro s
  unfold l19enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5697 8420 8424

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_sm8424 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8424 =
      denoteGraphDistributedFaithful sm initSM 5697 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 757 l19enSmMulti2
    5697 8424 (fun x => x)
    (by native_decide) l19en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_sm 758) (l19en_sm_not_written 758 8424 (by decide))
    (l19en_nonempty_sm 757) (l19en_sm_not_written 757 5697 (by decide))
  intro s
  unfold l19enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5697 8420 8424 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16531 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16531 =
      denoteGraphDistributedFaithful pm initPM 10921 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1576 l19enPmMulti2R0
    10921 16531 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1577) (l19en_pm_not_written 1577 16531 (by decide))
    (l19en_nonempty_pm 1576) (l19en_pm_not_written 1576 10921 (by decide))
  intro s
  unfold l19enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 10921 16531 16535

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16535 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16535 =
      denoteGraphDistributedFaithful pm initPM 10921 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1576 l19enPmMulti2R0
    10921 16535 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1577) (l19en_pm_not_written 1577 16535 (by decide))
    (l19en_nonempty_pm 1576) (l19en_pm_not_written 1576 10921 (by decide))
  intro s
  unfold l19enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 10921 16531 16535 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16539 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16539 =
      denoteGraphDistributedFaithful pm initPM 10922 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1577 l19enPmMulti2R1
    10922 16539 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1578) (l19en_pm_not_written 1578 16539 (by decide))
    (l19en_nonempty_pm 1577) (l19en_pm_not_written 1577 10922 (by decide))
  intro s
  unfold l19enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 10922 16539 16543

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16543 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16543 =
      denoteGraphDistributedFaithful pm initPM 10922 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1577 l19enPmMulti2R1
    10922 16543 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1578) (l19en_pm_not_written 1578 16543 (by decide))
    (l19en_nonempty_pm 1577) (l19en_pm_not_written 1577 10922 (by decide))
  intro s
  unfold l19enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 10922 16539 16543 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_sm5699 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5699 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8420)
        (denoteGraphDistributedFaithful sm initSM 5698) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 758 l19enSmRms5699
    8420 5698 5699 fw_rms_norm
    (by native_decide) l19en_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_sm 759) (l19en_sm_not_written 759 5699 (by decide))
    (l19en_nonempty_sm 758) (l19en_sm_not_written 758 8420 (by decide))
    (l19en_w5698_sm_drop 758)
  intro s
  unfold l19enSmRms5699
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8420 5698 5699

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10925 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10925 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16531)
        (denoteGraphDistributedFaithful pm initPM 5698) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1578 l19enPmRms10925
    16531 5698 10925 fw_rms_norm
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1579) (l19en_pm_not_written 1579 10925 (by decide))
    (l19en_nonempty_pm 1578) (l19en_pm_not_written 1578 16531 (by decide))
    (l19en_w5698_pm_drop 1578)
  intro s
  unfold l19enPmRms10925
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16531 5698 10925

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm10926 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10926 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16539)
        (denoteGraphDistributedFaithful pm initPM 5698) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1579 l19enPmRms10926
    16539 5698 10926 fw_rms_norm
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1580) (l19en_pm_not_written 1580 10926 (by decide))
    (l19en_nonempty_pm 1579) (l19en_pm_not_written 1579 16539 (by decide))
    (l19en_w5698_pm_drop 1579)
  intro s
  unfold l19enPmRms10926
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16539 5698 10926

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_sm8431 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8431 =
      denoteGraphDistributedFaithful sm initSM 5699 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 759 l19enSmMulti5
    5699 8431 (fun x => x)
    (by native_decide) l19en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l19en_nonempty_sm 760) (l19en_sm_not_written 760 8431 (by decide))
    (l19en_nonempty_sm 759) (l19en_sm_not_written 759 5699 (by decide))
  intro s
  unfold l19enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l19en_multiref5_first_out sm s 0 5699 8431 8435 8439 8443 8447

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_sm8435 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8435 =
      denoteGraphDistributedFaithful sm initSM 5699 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 759 l19enSmMulti5
    5699 8435 (fun x => x)
    (by native_decide) l19en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l19en_nonempty_sm 760) (l19en_sm_not_written 760 8435 (by decide))
    (l19en_nonempty_sm 759) (l19en_sm_not_written 759 5699 (by decide))
  intro s
  unfold l19enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out sm s 0 5699 8431 8435 8439 8443 8447
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_sm8439 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8439 =
      denoteGraphDistributedFaithful sm initSM 5699 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 759 l19enSmMulti5
    5699 8439 (fun x => x)
    (by native_decide) l19en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l19en_nonempty_sm 760) (l19en_sm_not_written 760 8439 (by decide))
    (l19en_nonempty_sm 759) (l19en_sm_not_written 759 5699 (by decide))
  intro s
  unfold l19enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out sm s 0 5699 8431 8435 8439 8443 8447
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_sm8443 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8443 =
      denoteGraphDistributedFaithful sm initSM 5699 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 759 l19enSmMulti5
    5699 8443 (fun x => x)
    (by native_decide) l19en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l19en_nonempty_sm 760) (l19en_sm_not_written 760 8443 (by decide))
    (l19en_nonempty_sm 759) (l19en_sm_not_written 759 5699 (by decide))
  intro s
  unfold l19enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out sm s 0 5699 8431 8435 8439 8443 8447
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_sm8447 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8447 =
      denoteGraphDistributedFaithful sm initSM 5699 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 759 l19enSmMulti5
    5699 8447 (fun x => x)
    (by native_decide) l19en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l19en_nonempty_sm 760) (l19en_sm_not_written 760 8447 (by decide))
    (l19en_nonempty_sm 759) (l19en_sm_not_written 759 5699 (by decide))
  intro s
  unfold l19enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out sm s 0 5699 8431 8435 8439 8443 8447
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16550 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16550 =
      denoteGraphDistributedFaithful pm initPM 10925 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1580 l19enPmMulti5R0
    10925 16550 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1581) (l19en_pm_not_written 1581 16550 (by decide))
    (l19en_nonempty_pm 1580) (l19en_pm_not_written 1580 10925 (by decide))
  intro s
  unfold l19enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l19en_multiref5_first_out pm s 0 10925 16550 16554 16558 16562 16566

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16554 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16554 =
      denoteGraphDistributedFaithful pm initPM 10925 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1580 l19enPmMulti5R0
    10925 16554 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1581) (l19en_pm_not_written 1581 16554 (by decide))
    (l19en_nonempty_pm 1580) (l19en_pm_not_written 1580 10925 (by decide))
  intro s
  unfold l19enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 0 10925 16550 16554 16558 16562 16566
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16558 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16558 =
      denoteGraphDistributedFaithful pm initPM 10925 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1580 l19enPmMulti5R0
    10925 16558 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1581) (l19en_pm_not_written 1581 16558 (by decide))
    (l19en_nonempty_pm 1580) (l19en_pm_not_written 1580 10925 (by decide))
  intro s
  unfold l19enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 0 10925 16550 16554 16558 16562 16566
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16562 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16562 =
      denoteGraphDistributedFaithful pm initPM 10925 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1580 l19enPmMulti5R0
    10925 16562 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1581) (l19en_pm_not_written 1581 16562 (by decide))
    (l19en_nonempty_pm 1580) (l19en_pm_not_written 1580 10925 (by decide))
  intro s
  unfold l19enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 0 10925 16550 16554 16558 16562 16566
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16566 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16566 =
      denoteGraphDistributedFaithful pm initPM 10925 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1580 l19enPmMulti5R0
    10925 16566 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19en_nonempty_pm 1581) (l19en_pm_not_written 1581 16566 (by decide))
    (l19en_nonempty_pm 1580) (l19en_pm_not_written 1580 10925 (by decide))
  intro s
  unfold l19enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 0 10925 16550 16554 16558 16562 16566
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16573 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16573 =
      denoteGraphDistributedFaithful pm initPM 10926 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1581 l19enPmMulti5R1
    10926 16573 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l19en_nonempty_pm 1582) (l19en_pm_not_written 1582 16573 (by decide))
    (l19en_nonempty_pm 1581) (l19en_pm_not_written 1581 10926 (by decide))
  intro s
  unfold l19enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l19en_multiref5_first_out pm s 1 10926 16573 16577 16581 16585 16589

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16577 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16577 =
      denoteGraphDistributedFaithful pm initPM 10926 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1581 l19enPmMulti5R1
    10926 16577 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l19en_nonempty_pm 1582) (l19en_pm_not_written 1582 16577 (by decide))
    (l19en_nonempty_pm 1581) (l19en_pm_not_written 1581 10926 (by decide))
  intro s
  unfold l19enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 1 10926 16573 16577 16581 16585 16589
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16581 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16581 =
      denoteGraphDistributedFaithful pm initPM 10926 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1581 l19enPmMulti5R1
    10926 16581 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l19en_nonempty_pm 1582) (l19en_pm_not_written 1582 16581 (by decide))
    (l19en_nonempty_pm 1581) (l19en_pm_not_written 1581 10926 (by decide))
  intro s
  unfold l19enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 1 10926 16573 16577 16581 16585 16589
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16585 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16585 =
      denoteGraphDistributedFaithful pm initPM 10926 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1581 l19enPmMulti5R1
    10926 16585 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l19en_nonempty_pm 1582) (l19en_pm_not_written 1582 16585 (by decide))
    (l19en_nonempty_pm 1581) (l19en_pm_not_written 1581 10926 (by decide))
  intro s
  unfold l19enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 1 10926 16573 16577 16581 16585 16589
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19en_red_pm16589 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16589 =
      denoteGraphDistributedFaithful pm initPM 10926 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1581 l19enPmMulti5R1
    10926 16589 (fun x => x)
    (by native_decide) l19en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l19en_nonempty_pm 1582) (l19en_pm_not_written 1582 16589 (by decide))
    (l19en_nonempty_pm 1581) (l19en_pm_not_written 1581 10926 (by decide))
  intro s
  unfold l19enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 1 10926 16573 16577 16581 16585 16589
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5691 (`FW_reshape` of 5690).
theorem recon_zigzagGoal_5691_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5691)
      (denoteGraphDistributedFaithful pm initPM 10893)
      (denoteGraphDistributedFaithful pm initPM 10894)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5690_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19en_red_sm5691 initSM, l19en_red_pm10893 initPM, l19en_red_pm10894 initPM]
  exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hparent (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5692 (`FW_reshape` of 5691).
theorem recon_zigzagGoal_5692_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5692)
      (denoteGraphDistributedFaithful pm initPM 10899)
      (denoteGraphDistributedFaithful pm initPM 10900)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5691_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19en_red_sm5692 initSM, l19en_red_pm10899 initPM, l19en_red_pm10900 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5694 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5694_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5694)
      (denoteGraphDistributedFaithful pm initPM 10903)
      (denoteGraphDistributedFaithful pm initPM 10904)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5692_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5693 = initPM 5693 :=
    recon_weight initSM initPM hInit initGoal_5693 (by native_decide) 5693
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5693 = initSM 5693 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5693
      layer1_sm_nodes_nonempty (fun n hn => (l19en_weights_not_written.1 n hn).1)
  have hpw : denoteGraphDistributedFaithful pm initPM 5693 = initPM 5693 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5693
      layer1_pm_nodes_nonempty (fun n hn => (l19en_weights_not_written.2 n hn).1)
  have hw : denoteGraphDistributedFaithful sm initSM 5693 =
      denoteGraphDistributedFaithful pm initPM 5693 := by
    rw [hsw, hpw]; exact hwInit
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5693).shape =
      [1024, 1024] := by
    rw [hpw]
    exact hPM 5693 [1024, 1024] (by native_decide)
  rw [l19en_red_sm5694 initSM, l19en_red_pm10903 initPM, l19en_red_pm10904 initPM, hw]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5695 (`FW_view` of 5694).
theorem recon_zigzagGoal_5695_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5695)
      (denoteGraphDistributedFaithful pm initPM 10913)
      (denoteGraphDistributedFaithful pm initPM 10914)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5694_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19en_red_sm5695 initSM, l19en_red_pm10913 initPM, l19en_red_pm10914 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5696 (`FW_float` of 5695).
theorem recon_zigzagGoal_5696_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5696)
      (denoteGraphDistributedFaithful pm initPM 10917)
      (denoteGraphDistributedFaithful pm initPM 10918)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5695_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19en_red_sm5696 initSM, l19en_red_pm10917 initPM, l19en_red_pm10918 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5697 (residual `FW_add` of the
-- cross-layer bypass 8416 and 5696).
theorem recon_zigzagGoal_5697_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5697)
      (denoteGraphDistributedFaithful pm initPM 10921)
      (denoteGraphDistributedFaithful pm initPM 10922)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8416_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5696_faithful initSM initPM hSM hPM hInit hValues hCu
  have pmFinal (tid : Tid) (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hw
  have h5639_5688 : denoteGraphDistributedFaithful pm initPM 5639 =
      denoteGraphDistributedFaithful pm initPM 5688 := by
    rw [pmFinal 5639 (fun n hn => (l19en_cu_not_written n hn).1),
      pmFinal 5688 (fun n hn => (l19en_cu_not_written n hn).2)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  rw [h5639_5688] at hA
  rw [l19en_red_sm5697 initSM, l19en_red_pm10921 initPM, l19en_red_pm10922 initPM]
  exact Zigzag2Rel.add 2048 1024 hA hB (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8420 (2-way multiref, position 0).
theorem recon_zigzagGoal_8420_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8420)
      (denoteGraphDistributedFaithful pm initPM 16531)
      (denoteGraphDistributedFaithful pm initPM 16539)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5697_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19en_red_sm8420 initSM, l19en_red_pm16531 initPM, l19en_red_pm16539 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8424 (2-way multiref, position 1).
theorem recon_zigzagGoal_8424_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8424)
      (denoteGraphDistributedFaithful pm initPM 16535)
      (denoteGraphDistributedFaithful pm initPM 16543)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5697_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19en_red_sm8424 initSM, l19en_red_pm16535 initPM, l19en_red_pm16543 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5699 (`FW_rms_norm` of 8420 with
-- the replicated weight 5698).
theorem recon_zigzagGoal_5699_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5699)
      (denoteGraphDistributedFaithful pm initPM 10925)
      (denoteGraphDistributedFaithful pm initPM 10926)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8420_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5698 = initPM 5698 :=
    recon_weight initSM initPM hInit initGoal_5698 (by native_decide) 5698
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5698 = initSM 5698 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5698
      layer1_sm_nodes_nonempty (fun n hn => (l19en_weights_not_written.1 n hn).2)
  have hpw : denoteGraphDistributedFaithful pm initPM 5698 = initPM 5698 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5698
      layer1_pm_nodes_nonempty (fun n hn => (l19en_weights_not_written.2 n hn).2)
  have hw : denoteGraphDistributedFaithful sm initSM 5698 =
      denoteGraphDistributedFaithful pm initPM 5698 := by
    rw [hsw, hpw]; exact hwInit
  rw [l19en_red_sm5699 initSM, l19en_red_pm10925 initPM, l19en_red_pm10926 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8431 (5-way multiref, position 0).
theorem recon_zigzagGoal_8431_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8431)
      (denoteGraphDistributedFaithful pm initPM 16550)
      (denoteGraphDistributedFaithful pm initPM 16573)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5699_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19en_red_sm8431 initSM, l19en_red_pm16550 initPM, l19en_red_pm16573 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8435 (5-way multiref, position 1).
theorem recon_zigzagGoal_8435_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8435)
      (denoteGraphDistributedFaithful pm initPM 16554)
      (denoteGraphDistributedFaithful pm initPM 16577)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5699_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19en_red_sm8435 initSM, l19en_red_pm16554 initPM, l19en_red_pm16577 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8439 (5-way multiref, position 2).
theorem recon_zigzagGoal_8439_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8439)
      (denoteGraphDistributedFaithful pm initPM 16558)
      (denoteGraphDistributedFaithful pm initPM 16581)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5699_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19en_red_sm8439 initSM, l19en_red_pm16558 initPM, l19en_red_pm16581 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8443 (5-way multiref, position 3).
theorem recon_zigzagGoal_8443_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8443)
      (denoteGraphDistributedFaithful pm initPM 16562)
      (denoteGraphDistributedFaithful pm initPM 16585)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5699_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19en_red_sm8443 initSM, l19en_red_pm16562 initPM, l19en_red_pm16585 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8447 (5-way multiref, position 4).
theorem recon_zigzagGoal_8447_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8447)
      (denoteGraphDistributedFaithful pm initPM 16566)
      (denoteGraphDistributedFaithful pm initPM 16589)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5699_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19en_red_sm8447 initSM, l19en_red_pm16566 initPM, l19en_red_pm16589 initPM]
  exact hparent

end
end TrainVerify.Denote.GeneratedPatterns
