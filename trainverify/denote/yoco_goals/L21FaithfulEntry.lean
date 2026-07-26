/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L21FaithfulZigzagAttention
import denote.yoco_goals.L20FaithfulBlockTail
import denote.yoco_goals.L12FaithfulRouterEntry

/-!
# Faithful zigzag relations for the block-9 entry segment

Continuation of `recon_zigzagGoal_5788_faithful` (block-9 cross-decoder
attention) through the block-9 entry segment:

* SM 821: `FW_reshape [5788] → [5789]`   (PM 1704/1705: `11235 → 11237`, `11236 → 11238`)
* SM 822: `FW_reshape [5789] → [5790]`   (PM 1706/1707: `11237 → 11243`, `11238 → 11244`)
* SM 823: `FW_mix_precision_linear [5790, 5791] → [5792]`
                                          (PM 1708/1709 with replicated weight 5791)
* SM 824: `FW_view [5792] → [5793]`      (PM 1710/1711)
* SM 825: `FW_float [5793] → [5794]`     (PM 1712/1713)
* SM 826: `FW_add [8494, 5794] → [5795]` (PM 1714/1715 with bypass 16675/16683)
* SM 827: `FW_multiref [5795] → [8498, 8502]`
                                          (PM 1716: `[16687, 16691]`, PM 1717: `[16695, 16699]`)
* SM 828: `FW_rms_norm [8498, 5796] → [5797]` (PM 1718/1719, replicated weight 5796)
* SM 829: `FW_multiref [5797] → [8509, 8513, 8517, 8521, 8525]`
                                          (PM 1720: `[16706, 16710, 16714, 16718, 16722]`,
                                           PM 1721: `[16729, 16733, 16737, 16741, 16745]`)

All relations are stated against the block-9 cumulative-sequence metadata tensor
`5786` (the same cu slot used by `recon_zigzagGoal_5788_faithful`).
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

private theorem l21en_multiref5_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 t4 t5 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := [t1, t2, t3, t4, t5], params := [5] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3, t4, t5].zip (List.replicate 5 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ### Node literals -/

private def l21enSmReshape5789 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5788], outs := [5789],
    params := [4096, 1024] }
private def l21enSmReshape5790 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5789], outs := [5790],
    params := [4096, 1024] }
private def l21enSmLinear5792 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5790, 5791],
    outs := [5792] }
private def l21enSmView5793 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5792], outs := [5793],
    params := [4096, 1024] }
private def l21enSmFloat5794 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5793], outs := [5794] }
private def l21enSmAdd5795 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8494, 5794], outs := [5795] }
private def l21enSmMulti2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5795], outs := [8498, 8502],
    params := [2] }
private def l21enSmRms5797 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8498, 5796], outs := [5797] }
private def l21enSmMulti5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5797],
    outs := [8509, 8513, 8517, 8521, 8525], params := [5] }

private def l21enPmReshape11237 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11235], outs := [11237],
    params := [2048, 1024] }
private def l21enPmReshape11238 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11236], outs := [11238],
    params := [2048, 1024] }
private def l21enPmReshape11243 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11237], outs := [11243],
    params := [2048, 1024] }
private def l21enPmReshape11244 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11238], outs := [11244],
    params := [2048, 1024] }
private def l21enPmLinear11247 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11243, 5791],
    outs := [11247] }
private def l21enPmLinear11248 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11244, 5791],
    outs := [11248] }
private def l21enPmView11257 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11247], outs := [11257],
    params := [2048, 1024] }
private def l21enPmView11258 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11248], outs := [11258],
    params := [2048, 1024] }
private def l21enPmFloat11261 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11257], outs := [11261] }
private def l21enPmFloat11262 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11258], outs := [11262] }
private def l21enPmAdd11265 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16675, 11261], outs := [11265] }
private def l21enPmAdd11266 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16683, 11262], outs := [11266] }
private def l21enPmMulti2R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11265], outs := [16687, 16691],
    params := [2] }
private def l21enPmMulti2R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11266], outs := [16695, 16699],
    params := [2] }
private def l21enPmRms11269 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16687, 5796], outs := [11269] }
private def l21enPmRms11270 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16695, 5796], outs := [11270] }
private def l21enPmMulti5R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11269],
    outs := [16706, 16710, 16714, 16718, 16722], params := [5] }
private def l21enPmMulti5R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11270],
    outs := [16729, 16733, 16737, 16741, 16745], params := [5] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l21en_sm_node_facts :
    sm.nodes[821]'(by native_decide) = l21enSmReshape5789 ∧
    sm.nodes[822]'(by native_decide) = l21enSmReshape5790 ∧
    sm.nodes[823]'(by native_decide) = l21enSmLinear5792 ∧
    sm.nodes[824]'(by native_decide) = l21enSmView5793 ∧
    sm.nodes[825]'(by native_decide) = l21enSmFloat5794 ∧
    sm.nodes[826]'(by native_decide) = l21enSmAdd5795 ∧
    sm.nodes[827]'(by native_decide) = l21enSmMulti2 ∧
    sm.nodes[828]'(by native_decide) = l21enSmRms5797 ∧
    sm.nodes[829]'(by native_decide) = l21enSmMulti5 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l21en_pm_node_facts :
    pm.nodes[1704]'(by native_decide) = l21enPmReshape11237 ∧
    pm.nodes[1705]'(by native_decide) = l21enPmReshape11238 ∧
    pm.nodes[1706]'(by native_decide) = l21enPmReshape11243 ∧
    pm.nodes[1707]'(by native_decide) = l21enPmReshape11244 ∧
    pm.nodes[1708]'(by native_decide) = l21enPmLinear11247 ∧
    pm.nodes[1709]'(by native_decide) = l21enPmLinear11248 ∧
    pm.nodes[1710]'(by native_decide) = l21enPmView11257 ∧
    pm.nodes[1711]'(by native_decide) = l21enPmView11258 ∧
    pm.nodes[1712]'(by native_decide) = l21enPmFloat11261 ∧
    pm.nodes[1713]'(by native_decide) = l21enPmFloat11262 ∧
    pm.nodes[1714]'(by native_decide) = l21enPmAdd11265 ∧
    pm.nodes[1715]'(by native_decide) = l21enPmAdd11266 ∧
    pm.nodes[1716]'(by native_decide) = l21enPmMulti2R0 ∧
    pm.nodes[1717]'(by native_decide) = l21enPmMulti2R1 ∧
    pm.nodes[1718]'(by native_decide) = l21enPmRms11269 ∧
    pm.nodes[1719]'(by native_decide) = l21enPmRms11270 ∧
    pm.nodes[1720]'(by native_decide) = l21enPmMulti5R0 ∧
    pm.nodes[1721]'(by native_decide) = l21enPmMulti5R1 := by
  native_decide

private theorem l21en_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l21en_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l21en_weights_not_written :
    (∀ n ∈ sm.nodes, 5791 ∉ n.outs ∧ 5796 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5791 ∉ n.outs ∧ 5796 ∉ n.outs) := by
  native_decide

private theorem l21en_w5791_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5791 ∉ n.outs := by
  intro n hn
  exact (l21en_weights_not_written.1 n (List.mem_of_mem_drop hn)).1

private theorem l21en_w5791_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5791 ∉ n.outs := by
  intro n hn
  exact (l21en_weights_not_written.2 n (List.mem_of_mem_drop hn)).1

private theorem l21en_w5796_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5796 ∉ n.outs := by
  intro n hn
  exact (l21en_weights_not_written.1 n (List.mem_of_mem_drop hn)).2

private theorem l21en_w5796_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5796 ∉ n.outs := by
  intro n hn
  exact (l21en_weights_not_written.2 n (List.mem_of_mem_drop hn)).2

set_option maxRecDepth 1000000 in
private theorem l21en_cu_not_written :
    ∀ n ∈ pm.nodes, 5737 ∉ n.outs ∧ 5786 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l21en_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(822, 5789), (821, 5788), (823, 5790), (824, 5792), (825, 5793), (826,
      5794), (827, 5795), (826, 8494), (828, 8498), (828, 8502), (829, 5797),
      (830, 8509), (830, 8513), (830, 8517), (830, 8521), (830, 8525)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l21en_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1705, 11237), (1704, 11235), (1706, 11238), (1705, 11236), (1707, 11243),
      (1706, 11237), (1708, 11244), (1707, 11238), (1709, 11247), (1708, 11243),
      (1710, 11248), (1709, 11244), (1711, 11257), (1710, 11247), (1712, 11258),
      (1711, 11248), (1713, 11261), (1712, 11257), (1714, 11262), (1713, 11258),
      (1715, 11265), (1714, 16675), (1714, 11261), (1716, 11266), (1715, 16683),
      (1715, 11262), (1717, 16687), (1717, 16691), (1716, 11265), (1718, 16695),
      (1718, 16699), (1717, 11266), (1719, 11269), (1718, 16687), (1720, 11270),
      (1719, 16695), (1721, 16706), (1721, 16710), (1721, 16714), (1721, 16718),
      (1721, 16722), (1720, 11269), (1722, 16729), (1722, 16733), (1722, 16737),
      (1722, 16741), (1722, 16745), (1721, 11270)]) :
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
private theorem l21en_red_sm5789 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5789 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5788) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 821 l21enSmReshape5789
    5788 5789 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l21en_sm_node_facts.1 ?_
    (l21en_nonempty_sm 822) (l21en_sm_not_written 822 5789 (by decide))
    (l21en_nonempty_sm 821) (l21en_sm_not_written 821 5788 (by decide))
  intro s
  unfold l21enSmReshape5789
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5788 5789 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11237 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11237 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11235) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1704 l21enPmReshape11237
    11235 11237 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l21en_pm_node_facts.1 ?_
    (l21en_nonempty_pm 1705) (l21en_pm_not_written 1705 11237 (by decide))
    (l21en_nonempty_pm 1704) (l21en_pm_not_written 1704 11235 (by decide))
  intro s
  unfold l21enPmReshape11237
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 11235 11237 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11238 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11238 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11236) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1705 l21enPmReshape11238
    11236 11238 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l21en_pm_node_facts.2.1 ?_
    (l21en_nonempty_pm 1706) (l21en_pm_not_written 1706 11238 (by decide))
    (l21en_nonempty_pm 1705) (l21en_pm_not_written 1705 11236 (by decide))
  intro s
  unfold l21enPmReshape11238
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 11236 11238 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_sm5790 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5790 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5789) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 822 l21enSmReshape5790
    5789 5790 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l21en_sm_node_facts.2.1 ?_
    (l21en_nonempty_sm 823) (l21en_sm_not_written 823 5790 (by decide))
    (l21en_nonempty_sm 822) (l21en_sm_not_written 822 5789 (by decide))
  intro s
  unfold l21enSmReshape5790
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5789 5790 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11243 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11243 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11237) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1706 l21enPmReshape11243
    11237 11243 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l21en_pm_node_facts.2.2.1 ?_
    (l21en_nonempty_pm 1707) (l21en_pm_not_written 1707 11243 (by decide))
    (l21en_nonempty_pm 1706) (l21en_pm_not_written 1706 11237 (by decide))
  intro s
  unfold l21enPmReshape11243
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 11237 11243 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11244 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11244 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11238) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1707 l21enPmReshape11244
    11238 11244 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l21en_pm_node_facts.2.2.2.1 ?_
    (l21en_nonempty_pm 1708) (l21en_pm_not_written 1708 11244 (by decide))
    (l21en_nonempty_pm 1707) (l21en_pm_not_written 1707 11238 (by decide))
  intro s
  unfold l21enPmReshape11244
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 11238 11244 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_sm5792 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5792 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5790)
        (denoteGraphDistributedFaithful sm initSM 5791) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 823 l21enSmLinear5792
    5790 5791 5792 fw_linear
    (by native_decide) l21en_sm_node_facts.2.2.1 ?_
    (l21en_nonempty_sm 824) (l21en_sm_not_written 824 5792 (by decide))
    (l21en_nonempty_sm 823) (l21en_sm_not_written 823 5790 (by decide))
    (l21en_w5791_sm_drop 823)
  intro s
  unfold l21enSmLinear5792
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5790 5791 5792

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11247 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11247 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11243)
        (denoteGraphDistributedFaithful pm initPM 5791) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1708 l21enPmLinear11247
    11243 5791 11247 fw_linear
    (by native_decide) l21en_pm_node_facts.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1709) (l21en_pm_not_written 1709 11247 (by decide))
    (l21en_nonempty_pm 1708) (l21en_pm_not_written 1708 11243 (by decide))
    (l21en_w5791_pm_drop 1708)
  intro s
  unfold l21enPmLinear11247
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11243 5791 11247

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11248 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11248 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11244)
        (denoteGraphDistributedFaithful pm initPM 5791) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1709 l21enPmLinear11248
    11244 5791 11248 fw_linear
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1710) (l21en_pm_not_written 1710 11248 (by decide))
    (l21en_nonempty_pm 1709) (l21en_pm_not_written 1709 11244 (by decide))
    (l21en_w5791_pm_drop 1709)
  intro s
  unfold l21enPmLinear11248
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11244 5791 11248

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_sm5793 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5793 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5792) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 824 l21enSmView5793
    5792 5793 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l21en_sm_node_facts.2.2.2.1 ?_
    (l21en_nonempty_sm 825) (l21en_sm_not_written 825 5793 (by decide))
    (l21en_nonempty_sm 824) (l21en_sm_not_written 824 5792 (by decide))
  intro s
  unfold l21enSmView5793
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5792 5793

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11257 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11257 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11247) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1710 l21enPmView11257
    11247 11257 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1711) (l21en_pm_not_written 1711 11257 (by decide))
    (l21en_nonempty_pm 1710) (l21en_pm_not_written 1710 11247 (by decide))
  intro s
  unfold l21enPmView11257
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 11247 11257

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11258 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11258 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11248) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1711 l21enPmView11258
    11248 11258 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1712) (l21en_pm_not_written 1712 11258 (by decide))
    (l21en_nonempty_pm 1711) (l21en_pm_not_written 1711 11248 (by decide))
  intro s
  unfold l21enPmView11258
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 11248 11258

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_sm5794 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5794 =
      denoteGraphDistributedFaithful sm initSM 5793 := by
  have h := denoteGraphDistributedFaithful_reduce1 sm initSM 825 l21enSmFloat5794
    5793 5794 id
    (by native_decide) l21en_sm_node_facts.2.2.2.2.1 ?_
    (l21en_nonempty_sm 826) (l21en_sm_not_written 826 5794 (by decide))
    (l21en_nonempty_sm 825) (l21en_sm_not_written 825 5793 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l21enSmFloat5794
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out sm s 0 5793 5794 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11261 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11261 =
      denoteGraphDistributedFaithful pm initPM 11257 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1712 l21enPmFloat11261
    11257 11261 id
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1713) (l21en_pm_not_written 1713 11261 (by decide))
    (l21en_nonempty_pm 1712) (l21en_pm_not_written 1712 11257 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l21enPmFloat11261
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 0 11257 11261 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11262 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11262 =
      denoteGraphDistributedFaithful pm initPM 11258 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1713 l21enPmFloat11262
    11258 11262 id
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1714) (l21en_pm_not_written 1714 11262 (by decide))
    (l21en_nonempty_pm 1713) (l21en_pm_not_written 1713 11258 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l21enPmFloat11262
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 1 11258 11262 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_sm5795 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5795 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8494)
        (denoteGraphDistributedFaithful sm initSM 5794) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 826 l21enSmAdd5795
    8494 5794 5795 elemwiseAdd
    (by native_decide) l21en_sm_node_facts.2.2.2.2.2.1 ?_
    (l21en_nonempty_sm 827) (l21en_sm_not_written 827 5795 (by decide))
    (l21en_nonempty_sm 826) (l21en_sm_not_written 826 8494 (by decide))
    (l21en_sm_not_written 826 5794 (by decide))
  intro s
  unfold l21enSmAdd5795
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8494 5794 5795

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11265 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11265 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16675)
        (denoteGraphDistributedFaithful pm initPM 11261) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1714 l21enPmAdd11265
    16675 11261 11265 elemwiseAdd
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1715) (l21en_pm_not_written 1715 11265 (by decide))
    (l21en_nonempty_pm 1714) (l21en_pm_not_written 1714 16675 (by decide))
    (l21en_pm_not_written 1714 11261 (by decide))
  intro s
  unfold l21enPmAdd11265
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16675 11261 11265

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11266 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11266 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16683)
        (denoteGraphDistributedFaithful pm initPM 11262) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1715 l21enPmAdd11266
    16683 11262 11266 elemwiseAdd
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1716) (l21en_pm_not_written 1716 11266 (by decide))
    (l21en_nonempty_pm 1715) (l21en_pm_not_written 1715 16683 (by decide))
    (l21en_pm_not_written 1715 11262 (by decide))
  intro s
  unfold l21enPmAdd11266
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16683 11262 11266

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_sm8498 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8498 =
      denoteGraphDistributedFaithful sm initSM 5795 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 827 l21enSmMulti2
    5795 8498 (fun x => x)
    (by native_decide) l21en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_sm 828) (l21en_sm_not_written 828 8498 (by decide))
    (l21en_nonempty_sm 827) (l21en_sm_not_written 827 5795 (by decide))
  intro s
  unfold l21enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5795 8498 8502

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_sm8502 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8502 =
      denoteGraphDistributedFaithful sm initSM 5795 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 827 l21enSmMulti2
    5795 8502 (fun x => x)
    (by native_decide) l21en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_sm 828) (l21en_sm_not_written 828 8502 (by decide))
    (l21en_nonempty_sm 827) (l21en_sm_not_written 827 5795 (by decide))
  intro s
  unfold l21enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5795 8498 8502 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16687 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16687 =
      denoteGraphDistributedFaithful pm initPM 11265 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1716 l21enPmMulti2R0
    11265 16687 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1717) (l21en_pm_not_written 1717 16687 (by decide))
    (l21en_nonempty_pm 1716) (l21en_pm_not_written 1716 11265 (by decide))
  intro s
  unfold l21enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 11265 16687 16691

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16691 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16691 =
      denoteGraphDistributedFaithful pm initPM 11265 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1716 l21enPmMulti2R0
    11265 16691 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1717) (l21en_pm_not_written 1717 16691 (by decide))
    (l21en_nonempty_pm 1716) (l21en_pm_not_written 1716 11265 (by decide))
  intro s
  unfold l21enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 11265 16687 16691 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16695 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16695 =
      denoteGraphDistributedFaithful pm initPM 11266 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1717 l21enPmMulti2R1
    11266 16695 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1718) (l21en_pm_not_written 1718 16695 (by decide))
    (l21en_nonempty_pm 1717) (l21en_pm_not_written 1717 11266 (by decide))
  intro s
  unfold l21enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 11266 16695 16699

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16699 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16699 =
      denoteGraphDistributedFaithful pm initPM 11266 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1717 l21enPmMulti2R1
    11266 16699 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1718) (l21en_pm_not_written 1718 16699 (by decide))
    (l21en_nonempty_pm 1717) (l21en_pm_not_written 1717 11266 (by decide))
  intro s
  unfold l21enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 11266 16695 16699 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_sm5797 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5797 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8498)
        (denoteGraphDistributedFaithful sm initSM 5796) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 828 l21enSmRms5797
    8498 5796 5797 fw_rms_norm
    (by native_decide) l21en_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_sm 829) (l21en_sm_not_written 829 5797 (by decide))
    (l21en_nonempty_sm 828) (l21en_sm_not_written 828 8498 (by decide))
    (l21en_w5796_sm_drop 828)
  intro s
  unfold l21enSmRms5797
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8498 5796 5797

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11269 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11269 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16687)
        (denoteGraphDistributedFaithful pm initPM 5796) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1718 l21enPmRms11269
    16687 5796 11269 fw_rms_norm
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1719) (l21en_pm_not_written 1719 11269 (by decide))
    (l21en_nonempty_pm 1718) (l21en_pm_not_written 1718 16687 (by decide))
    (l21en_w5796_pm_drop 1718)
  intro s
  unfold l21enPmRms11269
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16687 5796 11269

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm11270 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11270 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16695)
        (denoteGraphDistributedFaithful pm initPM 5796) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1719 l21enPmRms11270
    16695 5796 11270 fw_rms_norm
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1720) (l21en_pm_not_written 1720 11270 (by decide))
    (l21en_nonempty_pm 1719) (l21en_pm_not_written 1719 16695 (by decide))
    (l21en_w5796_pm_drop 1719)
  intro s
  unfold l21enPmRms11270
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16695 5796 11270

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_sm8509 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8509 =
      denoteGraphDistributedFaithful sm initSM 5797 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 829 l21enSmMulti5
    5797 8509 (fun x => x)
    (by native_decide) l21en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l21en_nonempty_sm 830) (l21en_sm_not_written 830 8509 (by decide))
    (l21en_nonempty_sm 829) (l21en_sm_not_written 829 5797 (by decide))
  intro s
  unfold l21enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l21en_multiref5_first_out sm s 0 5797 8509 8513 8517 8521 8525

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_sm8513 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8513 =
      denoteGraphDistributedFaithful sm initSM 5797 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 829 l21enSmMulti5
    5797 8513 (fun x => x)
    (by native_decide) l21en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l21en_nonempty_sm 830) (l21en_sm_not_written 830 8513 (by decide))
    (l21en_nonempty_sm 829) (l21en_sm_not_written 829 5797 (by decide))
  intro s
  unfold l21enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out sm s 0 5797 8509 8513 8517 8521 8525
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_sm8517 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8517 =
      denoteGraphDistributedFaithful sm initSM 5797 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 829 l21enSmMulti5
    5797 8517 (fun x => x)
    (by native_decide) l21en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l21en_nonempty_sm 830) (l21en_sm_not_written 830 8517 (by decide))
    (l21en_nonempty_sm 829) (l21en_sm_not_written 829 5797 (by decide))
  intro s
  unfold l21enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out sm s 0 5797 8509 8513 8517 8521 8525
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_sm8521 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8521 =
      denoteGraphDistributedFaithful sm initSM 5797 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 829 l21enSmMulti5
    5797 8521 (fun x => x)
    (by native_decide) l21en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l21en_nonempty_sm 830) (l21en_sm_not_written 830 8521 (by decide))
    (l21en_nonempty_sm 829) (l21en_sm_not_written 829 5797 (by decide))
  intro s
  unfold l21enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out sm s 0 5797 8509 8513 8517 8521 8525
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_sm8525 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8525 =
      denoteGraphDistributedFaithful sm initSM 5797 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 829 l21enSmMulti5
    5797 8525 (fun x => x)
    (by native_decide) l21en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l21en_nonempty_sm 830) (l21en_sm_not_written 830 8525 (by decide))
    (l21en_nonempty_sm 829) (l21en_sm_not_written 829 5797 (by decide))
  intro s
  unfold l21enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out sm s 0 5797 8509 8513 8517 8521 8525
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16706 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16706 =
      denoteGraphDistributedFaithful pm initPM 11269 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1720 l21enPmMulti5R0
    11269 16706 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1721) (l21en_pm_not_written 1721 16706 (by decide))
    (l21en_nonempty_pm 1720) (l21en_pm_not_written 1720 11269 (by decide))
  intro s
  unfold l21enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l21en_multiref5_first_out pm s 0 11269 16706 16710 16714 16718 16722

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16710 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16710 =
      denoteGraphDistributedFaithful pm initPM 11269 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1720 l21enPmMulti5R0
    11269 16710 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1721) (l21en_pm_not_written 1721 16710 (by decide))
    (l21en_nonempty_pm 1720) (l21en_pm_not_written 1720 11269 (by decide))
  intro s
  unfold l21enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 0 11269 16706 16710 16714 16718 16722
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16714 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16714 =
      denoteGraphDistributedFaithful pm initPM 11269 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1720 l21enPmMulti5R0
    11269 16714 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1721) (l21en_pm_not_written 1721 16714 (by decide))
    (l21en_nonempty_pm 1720) (l21en_pm_not_written 1720 11269 (by decide))
  intro s
  unfold l21enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 0 11269 16706 16710 16714 16718 16722
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16718 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16718 =
      denoteGraphDistributedFaithful pm initPM 11269 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1720 l21enPmMulti5R0
    11269 16718 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1721) (l21en_pm_not_written 1721 16718 (by decide))
    (l21en_nonempty_pm 1720) (l21en_pm_not_written 1720 11269 (by decide))
  intro s
  unfold l21enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 0 11269 16706 16710 16714 16718 16722
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16722 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16722 =
      denoteGraphDistributedFaithful pm initPM 11269 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1720 l21enPmMulti5R0
    11269 16722 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21en_nonempty_pm 1721) (l21en_pm_not_written 1721 16722 (by decide))
    (l21en_nonempty_pm 1720) (l21en_pm_not_written 1720 11269 (by decide))
  intro s
  unfold l21enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 0 11269 16706 16710 16714 16718 16722
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16729 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16729 =
      denoteGraphDistributedFaithful pm initPM 11270 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1721 l21enPmMulti5R1
    11270 16729 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l21en_nonempty_pm 1722) (l21en_pm_not_written 1722 16729 (by decide))
    (l21en_nonempty_pm 1721) (l21en_pm_not_written 1721 11270 (by decide))
  intro s
  unfold l21enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l21en_multiref5_first_out pm s 1 11270 16729 16733 16737 16741 16745

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16733 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16733 =
      denoteGraphDistributedFaithful pm initPM 11270 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1721 l21enPmMulti5R1
    11270 16733 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l21en_nonempty_pm 1722) (l21en_pm_not_written 1722 16733 (by decide))
    (l21en_nonempty_pm 1721) (l21en_pm_not_written 1721 11270 (by decide))
  intro s
  unfold l21enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 1 11270 16729 16733 16737 16741 16745
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16737 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16737 =
      denoteGraphDistributedFaithful pm initPM 11270 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1721 l21enPmMulti5R1
    11270 16737 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l21en_nonempty_pm 1722) (l21en_pm_not_written 1722 16737 (by decide))
    (l21en_nonempty_pm 1721) (l21en_pm_not_written 1721 11270 (by decide))
  intro s
  unfold l21enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 1 11270 16729 16733 16737 16741 16745
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16741 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16741 =
      denoteGraphDistributedFaithful pm initPM 11270 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1721 l21enPmMulti5R1
    11270 16741 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l21en_nonempty_pm 1722) (l21en_pm_not_written 1722 16741 (by decide))
    (l21en_nonempty_pm 1721) (l21en_pm_not_written 1721 11270 (by decide))
  intro s
  unfold l21enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 1 11270 16729 16733 16737 16741 16745
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21en_red_pm16745 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16745 =
      denoteGraphDistributedFaithful pm initPM 11270 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1721 l21enPmMulti5R1
    11270 16745 (fun x => x)
    (by native_decide) l21en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l21en_nonempty_pm 1722) (l21en_pm_not_written 1722 16745 (by decide))
    (l21en_nonempty_pm 1721) (l21en_pm_not_written 1721 11270 (by decide))
  intro s
  unfold l21enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 1 11270 16729 16733 16737 16741 16745
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5789 (`FW_reshape` of 5788).
theorem recon_zigzagGoal_5789_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5789)
      (denoteGraphDistributedFaithful pm initPM 11237)
      (denoteGraphDistributedFaithful pm initPM 11238)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5788_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21en_red_sm5789 initSM, l21en_red_pm11237 initPM, l21en_red_pm11238 initPM]
  exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hparent (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5790 (`FW_reshape` of 5789).
theorem recon_zigzagGoal_5790_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5790)
      (denoteGraphDistributedFaithful pm initPM 11243)
      (denoteGraphDistributedFaithful pm initPM 11244)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5789_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21en_red_sm5790 initSM, l21en_red_pm11243 initPM, l21en_red_pm11244 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5792 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5792_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5792)
      (denoteGraphDistributedFaithful pm initPM 11247)
      (denoteGraphDistributedFaithful pm initPM 11248)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5790_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5791 = initPM 5791 :=
    recon_weight initSM initPM hInit initGoal_5791 (by native_decide) 5791
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5791 = initSM 5791 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5791
      layer1_sm_nodes_nonempty (fun n hn => (l21en_weights_not_written.1 n hn).1)
  have hpw : denoteGraphDistributedFaithful pm initPM 5791 = initPM 5791 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5791
      layer1_pm_nodes_nonempty (fun n hn => (l21en_weights_not_written.2 n hn).1)
  have hw : denoteGraphDistributedFaithful sm initSM 5791 =
      denoteGraphDistributedFaithful pm initPM 5791 := by
    rw [hsw, hpw]; exact hwInit
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5791).shape =
      [1024, 1024] := by
    rw [hpw]
    exact hPM 5791 [1024, 1024] (by native_decide)
  rw [l21en_red_sm5792 initSM, l21en_red_pm11247 initPM, l21en_red_pm11248 initPM, hw]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5793 (`FW_view` of 5792).
theorem recon_zigzagGoal_5793_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5793)
      (denoteGraphDistributedFaithful pm initPM 11257)
      (denoteGraphDistributedFaithful pm initPM 11258)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5792_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21en_red_sm5793 initSM, l21en_red_pm11257 initPM, l21en_red_pm11258 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5794 (`FW_float` of 5793).
theorem recon_zigzagGoal_5794_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5794)
      (denoteGraphDistributedFaithful pm initPM 11261)
      (denoteGraphDistributedFaithful pm initPM 11262)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5793_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21en_red_sm5794 initSM, l21en_red_pm11261 initPM, l21en_red_pm11262 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5795 (residual `FW_add` of the
-- cross-layer bypass 8494 and 5794).
theorem recon_zigzagGoal_5795_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5795)
      (denoteGraphDistributedFaithful pm initPM 11265)
      (denoteGraphDistributedFaithful pm initPM 11266)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8494_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5794_faithful initSM initPM hSM hPM hInit hValues hCu
  have pmFinal (tid : Tid) (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hw
  have h5737_5786 : denoteGraphDistributedFaithful pm initPM 5737 =
      denoteGraphDistributedFaithful pm initPM 5786 := by
    rw [pmFinal 5737 (fun n hn => (l21en_cu_not_written n hn).1),
      pmFinal 5786 (fun n hn => (l21en_cu_not_written n hn).2)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  rw [h5737_5786] at hA
  rw [l21en_red_sm5795 initSM, l21en_red_pm11265 initPM, l21en_red_pm11266 initPM]
  exact Zigzag2Rel.add 2048 1024 hA hB (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8498 (2-way multiref, position 0).
theorem recon_zigzagGoal_8498_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8498)
      (denoteGraphDistributedFaithful pm initPM 16687)
      (denoteGraphDistributedFaithful pm initPM 16695)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5795_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21en_red_sm8498 initSM, l21en_red_pm16687 initPM, l21en_red_pm16695 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8502 (2-way multiref, position 1).
theorem recon_zigzagGoal_8502_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8502)
      (denoteGraphDistributedFaithful pm initPM 16691)
      (denoteGraphDistributedFaithful pm initPM 16699)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5795_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21en_red_sm8502 initSM, l21en_red_pm16691 initPM, l21en_red_pm16699 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5797 (`FW_rms_norm` of 8498 with
-- the replicated weight 5796).
theorem recon_zigzagGoal_5797_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5797)
      (denoteGraphDistributedFaithful pm initPM 11269)
      (denoteGraphDistributedFaithful pm initPM 11270)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8498_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5796 = initPM 5796 :=
    recon_weight initSM initPM hInit initGoal_5796 (by native_decide) 5796
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5796 = initSM 5796 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5796
      layer1_sm_nodes_nonempty (fun n hn => (l21en_weights_not_written.1 n hn).2)
  have hpw : denoteGraphDistributedFaithful pm initPM 5796 = initPM 5796 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5796
      layer1_pm_nodes_nonempty (fun n hn => (l21en_weights_not_written.2 n hn).2)
  have hw : denoteGraphDistributedFaithful sm initSM 5796 =
      denoteGraphDistributedFaithful pm initPM 5796 := by
    rw [hsw, hpw]; exact hwInit
  rw [l21en_red_sm5797 initSM, l21en_red_pm11269 initPM, l21en_red_pm11270 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8509 (5-way multiref, position 0).
theorem recon_zigzagGoal_8509_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8509)
      (denoteGraphDistributedFaithful pm initPM 16706)
      (denoteGraphDistributedFaithful pm initPM 16729)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5797_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21en_red_sm8509 initSM, l21en_red_pm16706 initPM, l21en_red_pm16729 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8513 (5-way multiref, position 1).
theorem recon_zigzagGoal_8513_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8513)
      (denoteGraphDistributedFaithful pm initPM 16710)
      (denoteGraphDistributedFaithful pm initPM 16733)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5797_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21en_red_sm8513 initSM, l21en_red_pm16710 initPM, l21en_red_pm16733 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8517 (5-way multiref, position 2).
theorem recon_zigzagGoal_8517_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8517)
      (denoteGraphDistributedFaithful pm initPM 16714)
      (denoteGraphDistributedFaithful pm initPM 16737)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5797_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21en_red_sm8517 initSM, l21en_red_pm16714 initPM, l21en_red_pm16737 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8521 (5-way multiref, position 3).
theorem recon_zigzagGoal_8521_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8521)
      (denoteGraphDistributedFaithful pm initPM 16718)
      (denoteGraphDistributedFaithful pm initPM 16741)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5797_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21en_red_sm8521 initSM, l21en_red_pm16718 initPM, l21en_red_pm16741 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8525 (5-way multiref, position 4).
theorem recon_zigzagGoal_8525_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8525)
      (denoteGraphDistributedFaithful pm initPM 16722)
      (denoteGraphDistributedFaithful pm initPM 16745)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5797_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21en_red_sm8525 initSM, l21en_red_pm16722 initPM, l21en_red_pm16745 initPM]
  exact hparent

end
end TrainVerify.Denote.GeneratedPatterns
