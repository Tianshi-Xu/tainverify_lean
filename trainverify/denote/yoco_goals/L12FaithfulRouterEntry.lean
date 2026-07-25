/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L12FaithfulResidual

/-!
# Faithful zigzag relation for generated goals 8147 / 8151 / 5356 and the 5-way fan-out

Continuation of `recon_zigzagGoal_5354_faithful`:

* SM node 512: `FW_multiref [5354] → [8147, 8151]`, params `[2]`
  (PM 1086: `[9717] → [15985, 15989]`, PM 1087: `[9718] → [15993, 15997]`)
* SM node 513: `FW_rms_norm [8147, 5355] → [5356]`
  (PM 1088: `[15985, 5355] → [9721]`, PM 1089: `[15993, 5355] → [9722]`)
* SM node 514: `FW_multiref [5356] → [8158, 8162, 8166, 8170, 8174]`, params `[5]`
  (PM 1090: `[9721] → [16004, 16008, 16012, 16016, 16020]`,
   PM 1091: `[9722] → [16027, 16031, 16035, 16039, 16043]`)

Tensor 5355 is a replicated `[1024]` RMSNorm weight (`initGoal_5355`).

`FW_multiref` is a data identity on each of its outputs, so the zigzag relation is
simply inherited from the parent; the RMSNorm step uses `Zigzag2Rel.rms_norm`.
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

private theorem l12re_multiref5_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 t4 t5 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := [t1, t2, t3, t4, t5], params := [5] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3, t4, t5].zip (List.replicate 5 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ### Node literals -/

private def l12reSmMulti2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5354], outs := [8147, 8151],
    params := [2] }
private def l12rePmMulti2R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9717], outs := [15985, 15989],
    params := [2] }
private def l12rePmMulti2R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9718], outs := [15993, 15997],
    params := [2] }

private def l12reSmRms5356 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8147, 5355], outs := [5356] }
private def l12rePmRms9721 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15985, 5355], outs := [9721] }
private def l12rePmRms9722 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15993, 5355], outs := [9722] }

private def l12reSmMulti5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5356],
    outs := [8158, 8162, 8166, 8170, 8174], params := [5] }
private def l12rePmMulti5R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9721],
    outs := [16004, 16008, 16012, 16016, 16020], params := [5] }
private def l12rePmMulti5R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9722],
    outs := [16027, 16031, 16035, 16039, 16043], params := [5] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l12re_sm_node_facts :
    sm.nodes[512]'(by native_decide) = l12reSmMulti2 ∧
    sm.nodes[513]'(by native_decide) = l12reSmRms5356 ∧
    sm.nodes[514]'(by native_decide) = l12reSmMulti5 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12re_pm_node_facts :
    pm.nodes[1086]'(by native_decide) = l12rePmMulti2R0 ∧
    pm.nodes[1087]'(by native_decide) = l12rePmMulti2R1 ∧
    pm.nodes[1088]'(by native_decide) = l12rePmRms9721 ∧
    pm.nodes[1089]'(by native_decide) = l12rePmRms9722 ∧
    pm.nodes[1090]'(by native_decide) = l12rePmMulti5R0 ∧
    pm.nodes[1091]'(by native_decide) = l12rePmMulti5R1 := by
  native_decide

private theorem l12re_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l12re_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12re_weight5355_not_written :
    (∀ n ∈ sm.nodes, 5355 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5355 ∉ n.outs) := by
  native_decide

private theorem l12re_w5355_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5355 ∉ n.outs := by
  intro n hn
  exact l12re_weight5355_not_written.1 n (List.mem_of_mem_drop hn)

private theorem l12re_w5355_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5355 ∉ n.outs := by
  intro n hn
  exact l12re_weight5355_not_written.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12re_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(513, 8147), (513, 8151), (512, 5354),
      (514, 5356), (513, 8147),
      (515, 8158), (515, 8162), (515, 8166), (515, 8170), (515, 8174),
      (514, 5356)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12re_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1087, 15985), (1087, 15989), (1086, 9717),
      (1088, 15993), (1088, 15997), (1087, 9718),
      (1089, 9721), (1088, 15985), (1090, 9722), (1089, 15993),
      (1091, 16004), (1091, 16008), (1091, 16012), (1091, 16016), (1091, 16020),
      (1090, 9721),
      (1092, 16027), (1092, 16031), (1092, 16035), (1092, 16039), (1092, 16043),
      (1091, 9722)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions: 2-way multiref off 5354 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_sm8147 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8147 =
      denoteGraphDistributedFaithful sm initSM 5354 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 512 l12reSmMulti2
    5354 8147 (fun x => x)
    (by native_decide) l12re_sm_node_facts.1 ?_
    (l12re_nonempty_sm 513) (l12re_sm_not_written 513 8147 (by decide))
    (l12re_nonempty_sm 512) (l12re_sm_not_written 512 5354 (by decide))
  intro s
  unfold l12reSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5354 8147 8151

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_sm8151 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8151 =
      denoteGraphDistributedFaithful sm initSM 5354 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 512 l12reSmMulti2
    5354 8151 (fun x => x)
    (by native_decide) l12re_sm_node_facts.1 ?_
    (l12re_nonempty_sm 513) (l12re_sm_not_written 513 8151 (by decide))
    (l12re_nonempty_sm 512) (l12re_sm_not_written 512 5354 (by decide))
  intro s
  unfold l12reSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5354 8147 8151 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm15985 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 15985 =
      denoteGraphDistributedFaithful pm initPM 9717 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1086 l12rePmMulti2R0
    9717 15985 (fun x => x)
    (by native_decide) l12re_pm_node_facts.1 ?_
    (l12re_nonempty_pm 1087) (l12re_pm_not_written 1087 15985 (by decide))
    (l12re_nonempty_pm 1086) (l12re_pm_not_written 1086 9717 (by decide))
  intro s
  unfold l12rePmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 9717 15985 15989

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm15989 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 15989 =
      denoteGraphDistributedFaithful pm initPM 9717 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1086 l12rePmMulti2R0
    9717 15989 (fun x => x)
    (by native_decide) l12re_pm_node_facts.1 ?_
    (l12re_nonempty_pm 1087) (l12re_pm_not_written 1087 15989 (by decide))
    (l12re_nonempty_pm 1086) (l12re_pm_not_written 1086 9717 (by decide))
  intro s
  unfold l12rePmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 9717 15985 15989 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm15993 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 15993 =
      denoteGraphDistributedFaithful pm initPM 9718 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1087 l12rePmMulti2R1
    9718 15993 (fun x => x)
    (by native_decide) l12re_pm_node_facts.2.1 ?_
    (l12re_nonempty_pm 1088) (l12re_pm_not_written 1088 15993 (by decide))
    (l12re_nonempty_pm 1087) (l12re_pm_not_written 1087 9718 (by decide))
  intro s
  unfold l12rePmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 9718 15993 15997

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm15997 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 15997 =
      denoteGraphDistributedFaithful pm initPM 9718 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1087 l12rePmMulti2R1
    9718 15997 (fun x => x)
    (by native_decide) l12re_pm_node_facts.2.1 ?_
    (l12re_nonempty_pm 1088) (l12re_pm_not_written 1088 15997 (by decide))
    (l12re_nonempty_pm 1087) (l12re_pm_not_written 1087 9718 (by decide))
  intro s
  unfold l12rePmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 9718 15993 15997 (by decide)

/-! ### Node reductions: RMSNorm 5356 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_sm5356 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5356 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8147)
        (denoteGraphDistributedFaithful sm initSM 5355) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 513 l12reSmRms5356
    8147 5355 5356 fw_rms_norm
    (by native_decide) l12re_sm_node_facts.2.1 ?_
    (l12re_nonempty_sm 514) (l12re_sm_not_written 514 5356 (by decide))
    (l12re_nonempty_sm 513) (l12re_sm_not_written 513 8147 (by decide))
    (l12re_w5355_sm_drop 513)
  intro s
  unfold l12reSmRms5356
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8147 5355 5356

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm9721 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9721 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 15985)
        (denoteGraphDistributedFaithful pm initPM 5355) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1088 l12rePmRms9721
    15985 5355 9721 fw_rms_norm
    (by native_decide) l12re_pm_node_facts.2.2.1 ?_
    (l12re_nonempty_pm 1089) (l12re_pm_not_written 1089 9721 (by decide))
    (l12re_nonempty_pm 1088) (l12re_pm_not_written 1088 15985 (by decide))
    (l12re_w5355_pm_drop 1088)
  intro s
  unfold l12rePmRms9721
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 15985 5355 9721

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm9722 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9722 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 15993)
        (denoteGraphDistributedFaithful pm initPM 5355) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1089 l12rePmRms9722
    15993 5355 9722 fw_rms_norm
    (by native_decide) l12re_pm_node_facts.2.2.2.1 ?_
    (l12re_nonempty_pm 1090) (l12re_pm_not_written 1090 9722 (by decide))
    (l12re_nonempty_pm 1089) (l12re_pm_not_written 1089 15993 (by decide))
    (l12re_w5355_pm_drop 1089)
  intro s
  unfold l12rePmRms9722
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 15993 5355 9722

/-! ### Node reductions: 5-way multiref off 5356 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_sm8158 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8158 =
      denoteGraphDistributedFaithful sm initSM 5356 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 514 l12reSmMulti5
    5356 8158 (fun x => x)
    (by native_decide) l12re_sm_node_facts.2.2 ?_
    (l12re_nonempty_sm 515) (l12re_sm_not_written 515 8158 (by decide))
    (l12re_nonempty_sm 514) (l12re_sm_not_written 514 5356 (by decide))
  intro s
  unfold l12reSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l12re_multiref5_first_out sm s 0 5356 8158 8162 8166 8170 8174

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_sm8162 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8162 =
      denoteGraphDistributedFaithful sm initSM 5356 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 514 l12reSmMulti5
    5356 8162 (fun x => x)
    (by native_decide) l12re_sm_node_facts.2.2 ?_
    (l12re_nonempty_sm 515) (l12re_sm_not_written 515 8162 (by decide))
    (l12re_nonempty_sm 514) (l12re_sm_not_written 514 5356 (by decide))
  intro s
  unfold l12reSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out sm s 0 5356 8158 8162 8166 8170 8174 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_sm8166 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8166 =
      denoteGraphDistributedFaithful sm initSM 5356 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 514 l12reSmMulti5
    5356 8166 (fun x => x)
    (by native_decide) l12re_sm_node_facts.2.2 ?_
    (l12re_nonempty_sm 515) (l12re_sm_not_written 515 8166 (by decide))
    (l12re_nonempty_sm 514) (l12re_sm_not_written 514 5356 (by decide))
  intro s
  unfold l12reSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out sm s 0 5356 8158 8162 8166 8170 8174
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_sm8170 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8170 =
      denoteGraphDistributedFaithful sm initSM 5356 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 514 l12reSmMulti5
    5356 8170 (fun x => x)
    (by native_decide) l12re_sm_node_facts.2.2 ?_
    (l12re_nonempty_sm 515) (l12re_sm_not_written 515 8170 (by decide))
    (l12re_nonempty_sm 514) (l12re_sm_not_written 514 5356 (by decide))
  intro s
  unfold l12reSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out sm s 0 5356 8158 8162 8166 8170 8174
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_sm8174 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8174 =
      denoteGraphDistributedFaithful sm initSM 5356 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 514 l12reSmMulti5
    5356 8174 (fun x => x)
    (by native_decide) l12re_sm_node_facts.2.2 ?_
    (l12re_nonempty_sm 515) (l12re_sm_not_written 515 8174 (by decide))
    (l12re_nonempty_sm 514) (l12re_sm_not_written 514 5356 (by decide))
  intro s
  unfold l12reSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out sm s 0 5356 8158 8162 8166 8170 8174
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm16004 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16004 =
      denoteGraphDistributedFaithful pm initPM 9721 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1090 l12rePmMulti5R0
    9721 16004 (fun x => x)
    (by native_decide) l12re_pm_node_facts.2.2.2.2.1 ?_
    (l12re_nonempty_pm 1091) (l12re_pm_not_written 1091 16004 (by decide))
    (l12re_nonempty_pm 1090) (l12re_pm_not_written 1090 9721 (by decide))
  intro s
  unfold l12rePmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l12re_multiref5_first_out pm s 0 9721 16004 16008 16012 16016 16020

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm16008 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16008 =
      denoteGraphDistributedFaithful pm initPM 9721 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1090 l12rePmMulti5R0
    9721 16008 (fun x => x)
    (by native_decide) l12re_pm_node_facts.2.2.2.2.1 ?_
    (l12re_nonempty_pm 1091) (l12re_pm_not_written 1091 16008 (by decide))
    (l12re_nonempty_pm 1090) (l12re_pm_not_written 1090 9721 (by decide))
  intro s
  unfold l12rePmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 0 9721 16004 16008 16012 16016 16020 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm16012 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16012 =
      denoteGraphDistributedFaithful pm initPM 9721 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1090 l12rePmMulti5R0
    9721 16012 (fun x => x)
    (by native_decide) l12re_pm_node_facts.2.2.2.2.1 ?_
    (l12re_nonempty_pm 1091) (l12re_pm_not_written 1091 16012 (by decide))
    (l12re_nonempty_pm 1090) (l12re_pm_not_written 1090 9721 (by decide))
  intro s
  unfold l12rePmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 0 9721 16004 16008 16012 16016 16020
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm16016 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16016 =
      denoteGraphDistributedFaithful pm initPM 9721 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1090 l12rePmMulti5R0
    9721 16016 (fun x => x)
    (by native_decide) l12re_pm_node_facts.2.2.2.2.1 ?_
    (l12re_nonempty_pm 1091) (l12re_pm_not_written 1091 16016 (by decide))
    (l12re_nonempty_pm 1090) (l12re_pm_not_written 1090 9721 (by decide))
  intro s
  unfold l12rePmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 0 9721 16004 16008 16012 16016 16020
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm16020 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16020 =
      denoteGraphDistributedFaithful pm initPM 9721 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1090 l12rePmMulti5R0
    9721 16020 (fun x => x)
    (by native_decide) l12re_pm_node_facts.2.2.2.2.1 ?_
    (l12re_nonempty_pm 1091) (l12re_pm_not_written 1091 16020 (by decide))
    (l12re_nonempty_pm 1090) (l12re_pm_not_written 1090 9721 (by decide))
  intro s
  unfold l12rePmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 0 9721 16004 16008 16012 16016 16020
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm16027 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16027 =
      denoteGraphDistributedFaithful pm initPM 9722 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1091 l12rePmMulti5R1
    9722 16027 (fun x => x)
    (by native_decide) l12re_pm_node_facts.2.2.2.2.2 ?_
    (l12re_nonempty_pm 1092) (l12re_pm_not_written 1092 16027 (by decide))
    (l12re_nonempty_pm 1091) (l12re_pm_not_written 1091 9722 (by decide))
  intro s
  unfold l12rePmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l12re_multiref5_first_out pm s 1 9722 16027 16031 16035 16039 16043

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm16031 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16031 =
      denoteGraphDistributedFaithful pm initPM 9722 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1091 l12rePmMulti5R1
    9722 16031 (fun x => x)
    (by native_decide) l12re_pm_node_facts.2.2.2.2.2 ?_
    (l12re_nonempty_pm 1092) (l12re_pm_not_written 1092 16031 (by decide))
    (l12re_nonempty_pm 1091) (l12re_pm_not_written 1091 9722 (by decide))
  intro s
  unfold l12rePmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 1 9722 16027 16031 16035 16039 16043 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm16035 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16035 =
      denoteGraphDistributedFaithful pm initPM 9722 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1091 l12rePmMulti5R1
    9722 16035 (fun x => x)
    (by native_decide) l12re_pm_node_facts.2.2.2.2.2 ?_
    (l12re_nonempty_pm 1092) (l12re_pm_not_written 1092 16035 (by decide))
    (l12re_nonempty_pm 1091) (l12re_pm_not_written 1091 9722 (by decide))
  intro s
  unfold l12rePmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 1 9722 16027 16031 16035 16039 16043
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm16039 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16039 =
      denoteGraphDistributedFaithful pm initPM 9722 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1091 l12rePmMulti5R1
    9722 16039 (fun x => x)
    (by native_decide) l12re_pm_node_facts.2.2.2.2.2 ?_
    (l12re_nonempty_pm 1092) (l12re_pm_not_written 1092 16039 (by decide))
    (l12re_nonempty_pm 1091) (l12re_pm_not_written 1091 9722 (by decide))
  intro s
  unfold l12rePmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 1 9722 16027 16031 16035 16039 16043
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12re_red_pm16043 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16043 =
      denoteGraphDistributedFaithful pm initPM 9722 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1091 l12rePmMulti5R1
    9722 16043 (fun x => x)
    (by native_decide) l12re_pm_node_facts.2.2.2.2.2 ?_
    (l12re_nonempty_pm 1092) (l12re_pm_not_written 1092 16043 (by decide))
    (l12re_nonempty_pm 1091) (l12re_pm_not_written 1091 9722 (by decide))
  intro s
  unfold l12rePmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 1 9722 16027 16031 16035 16039 16043
    (by decide) (by decide) (by decide) (by decide)

/-! ### Goals -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8147 (multiref position 0 off 5354).
theorem recon_zigzagGoal_8147_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8147)
      (denoteGraphDistributedFaithful pm initPM 15985)
      (denoteGraphDistributedFaithful pm initPM 15993)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5354_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12re_red_sm8147 initSM, l12re_red_pm15985 initPM, l12re_red_pm15993 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8151 (multiref position 1 off 5354:
-- the cross-MoE residual bypass consumed later by `FW_add`).
theorem recon_zigzagGoal_8151_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8151)
      (denoteGraphDistributedFaithful pm initPM 15989)
      (denoteGraphDistributedFaithful pm initPM 15997)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5354_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12re_red_sm8151 initSM, l12re_red_pm15989 initPM, l12re_red_pm15997 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5356 (`FW_rms_norm` of 8147 with
-- the replicated weight 5355).
theorem recon_zigzagGoal_5356_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5356)
      (denoteGraphDistributedFaithful pm initPM 9721)
      (denoteGraphDistributedFaithful pm initPM 9722)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8147_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5355 = initPM 5355 :=
    recon_weight initSM initPM hInit initGoal_5355 (by native_decide) 5355
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5355 = initSM 5355 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5355
      layer1_sm_nodes_nonempty l12re_weight5355_not_written.1
  have hpw : denoteGraphDistributedFaithful pm initPM 5355 = initPM 5355 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5355
      layer1_pm_nodes_nonempty l12re_weight5355_not_written.2
  have hw : denoteGraphDistributedFaithful sm initSM 5355 =
      denoteGraphDistributedFaithful pm initPM 5355 := by
    rw [hsw, hpw]; exact hwInit
  rw [l12re_red_sm5356 initSM, l12re_red_pm9721 initPM, l12re_red_pm9722 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8158 (5-way multiref, position 0).
theorem recon_zigzagGoal_8158_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8158)
      (denoteGraphDistributedFaithful pm initPM 16004)
      (denoteGraphDistributedFaithful pm initPM 16027)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5356_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12re_red_sm8158 initSM, l12re_red_pm16004 initPM, l12re_red_pm16027 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8162 (5-way multiref, position 1).
theorem recon_zigzagGoal_8162_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8162)
      (denoteGraphDistributedFaithful pm initPM 16008)
      (denoteGraphDistributedFaithful pm initPM 16031)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5356_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12re_red_sm8162 initSM, l12re_red_pm16008 initPM, l12re_red_pm16031 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8166 (5-way multiref, position 2).
theorem recon_zigzagGoal_8166_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8166)
      (denoteGraphDistributedFaithful pm initPM 16012)
      (denoteGraphDistributedFaithful pm initPM 16035)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5356_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12re_red_sm8166 initSM, l12re_red_pm16012 initPM, l12re_red_pm16035 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8170 (5-way multiref, position 3).
theorem recon_zigzagGoal_8170_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8170)
      (denoteGraphDistributedFaithful pm initPM 16016)
      (denoteGraphDistributedFaithful pm initPM 16039)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5356_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12re_red_sm8170 initSM, l12re_red_pm16016 initPM, l12re_red_pm16039 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8174 (5-way multiref, position 4).
theorem recon_zigzagGoal_8174_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8174)
      (denoteGraphDistributedFaithful pm initPM 16020)
      (denoteGraphDistributedFaithful pm initPM 16043)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5356_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12re_red_sm8174 initSM, l12re_red_pm16020 initPM, l12re_red_pm16043 initPM]
  exact hparent

end
end TrainVerify.Denote.GeneratedPatterns
