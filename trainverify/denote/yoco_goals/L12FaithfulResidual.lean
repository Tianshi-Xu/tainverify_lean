/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L12FaithfulLinearChain
import denote.yoco_goals.L12FaithfulMaybeShuffle
import denote.yoco_goals.ZigzagPointwiseRel

/-!
# Faithful zigzag relation for generated goals 5353 / 5354

Continuation of `recon_zigzagGoal_5352_faithful`:

* SM node 510: `FW_float [5352] → [5353]` (PM 1082/1083: `[9709] → [9713]`,
  `[9710] → [9714]`)
* SM node 511: `FW_add [8143, 5353] → [5354]` (PM 1084/1085:
  `[15973, 9713] → [9717]`, `[15981, 9714] → [9718]`)

The residual bypass tensor `8143` is the **second** output (zero-based index 1)
of SM node 474 `FW_multiref [5338] → [8139, 8143]`; on the PM side it is
`15973` (rank 0, node 1006, from `9655`) and `15981` (rank 1, node 1009, from
`9656`).  Its zigzag relation is therefore inherited verbatim from
`recon_zigzagGoal_5338_distributed`.

`FW_float` is the identity in the model (`evalOp_fw_float`), and `FW_add`
denotes `elemwiseAdd` (`evalOp_fw_add2`), so the two steps are discharged by
transport along the identity and by `Zigzag2Rel.add` respectively.
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

private def l12SmFloat5353 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5352], outs := [5353] }
private def l12PmFloat9713 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9709], outs := [9713] }
private def l12PmFloat9714 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9710], outs := [9714] }

private def l12SmAdd5354 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8143, 5353], outs := [5354] }
private def l12PmAdd9717 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15973, 9713], outs := [9717] }
private def l12PmAdd9718 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15981, 9714], outs := [9718] }

private def l12SmMref474 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5338], outs := [8139, 8143],
    params := [2] }
private def l12PmMref1006 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9655], outs := [15969, 15973],
    params := [2] }
private def l12PmMref1009 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9656], outs := [15977, 15981],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem l12res_sm_node_facts :
    sm.nodes[510]'(by native_decide) = l12SmFloat5353 ∧
    sm.nodes[511]'(by native_decide) = l12SmAdd5354 ∧
    sm.nodes[474]'(by native_decide) = l12SmMref474 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12res_pm_node_facts :
    pm.nodes[1082]'(by native_decide) = l12PmFloat9713 ∧
    pm.nodes[1083]'(by native_decide) = l12PmFloat9714 ∧
    pm.nodes[1084]'(by native_decide) = l12PmAdd9717 ∧
    pm.nodes[1085]'(by native_decide) = l12PmAdd9718 ∧
    pm.nodes[1006]'(by native_decide) = l12PmMref1006 ∧
    pm.nodes[1009]'(by native_decide) = l12PmMref1009 := by
  native_decide

private theorem l12res_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l12res_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12res_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(511, 5353), (510, 5352), (512, 5354), (511, 8143),
      (475, 8143), (474, 5338)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12res_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1083, 9713), (1082, 9709), (1084, 9714), (1083, 9710),
      (1085, 9717), (1084, 15973), (1084, 9713),
      (1086, 9718), (1085, 15981), (1085, 9714),
      (1007, 15973), (1006, 9655), (1010, 15981), (1009, 9656)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12res_cu_not_written :
    (∀ n ∈ pm.nodes, 5337 ∉ n.outs ∧ 5345 ∉ n.outs) := by
  native_decide

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12res_red_sm5353 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5353 =
      denoteGraphDistributedFaithful sm initSM 5352 := by
  have h := denoteGraphDistributedFaithful_reduce1 sm initSM 510 l12SmFloat5353
    5352 5353 id
    (by native_decide) l12res_sm_node_facts.1 ?_
    (l12res_nonempty_sm 511) (l12res_sm_not_written 511 5353 (by decide))
    (l12res_nonempty_sm 510) (l12res_sm_not_written 510 5352 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l12SmFloat5353
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out sm s 0 5352 5353 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12res_red_pm9713 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9713 =
      denoteGraphDistributedFaithful pm initPM 9709 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1082 l12PmFloat9713
    9709 9713 id
    (by native_decide) l12res_pm_node_facts.1 ?_
    (l12res_nonempty_pm 1083) (l12res_pm_not_written 1083 9713 (by decide))
    (l12res_nonempty_pm 1082) (l12res_pm_not_written 1082 9709 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l12PmFloat9713
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 0 9709 9713 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12res_red_pm9714 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9714 =
      denoteGraphDistributedFaithful pm initPM 9710 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1083 l12PmFloat9714
    9710 9714 id
    (by native_decide) l12res_pm_node_facts.2.1 ?_
    (l12res_nonempty_pm 1084) (l12res_pm_not_written 1084 9714 (by decide))
    (l12res_nonempty_pm 1083) (l12res_pm_not_written 1083 9710 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l12PmFloat9714
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 1 9710 9714 []

/-! ### The 8143 residual bypass (second `FW_multiref` output of node 474) -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12res_red_sm8143 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8143 =
      denoteGraphDistributedFaithful sm initSM 5338 := by
  have h := denoteGraphDistributedFaithful_reduce1 sm initSM 474 l12SmMref474
    5338 8143 id
    (by native_decide) l12res_sm_node_facts.2.2 ?_
    (l12res_nonempty_sm 475) (l12res_sm_not_written 475 8143 (by decide))
    (l12res_nonempty_sm 474) (l12res_sm_not_written 474 5338 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l12SmMref474
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref2_second_out' sm s 0 5338 8139 8143 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12res_red_pm15973 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 15973 =
      denoteGraphDistributedFaithful pm initPM 9655 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1006 l12PmMref1006
    9655 15973 id
    (by native_decide) l12res_pm_node_facts.2.2.2.2.1 ?_
    (l12res_nonempty_pm 1007) (l12res_pm_not_written 1007 15973 (by decide))
    (l12res_nonempty_pm 1006) (l12res_pm_not_written 1006 9655 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l12PmMref1006
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref2_second_out' pm s 0 9655 15969 15973 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12res_red_pm15981 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 15981 =
      denoteGraphDistributedFaithful pm initPM 9656 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1009 l12PmMref1009
    9656 15981 id
    (by native_decide) l12res_pm_node_facts.2.2.2.2.2 ?_
    (l12res_nonempty_pm 1010) (l12res_pm_not_written 1010 15981 (by decide))
    (l12res_nonempty_pm 1009) (l12res_pm_not_written 1009 9656 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l12PmMref1009
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref2_second_out' pm s 1 9656 15977 15981 (by decide)

/-! ### `FW_add` reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12res_red_sm5354 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5354 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8143)
        (denoteGraphDistributedFaithful sm initSM 5353) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 511 l12SmAdd5354
    8143 5353 5354 elemwiseAdd
    (by native_decide) l12res_sm_node_facts.2.1 ?_
    (l12res_nonempty_sm 512) (l12res_sm_not_written 512 5354 (by decide))
    (l12res_nonempty_sm 511) (l12res_sm_not_written 511 8143 (by decide))
    (l12res_sm_not_written 511 5353 (by decide))
  intro s
  unfold l12SmAdd5354
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8143 5353 5354

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12res_red_pm9717 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9717 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 15973)
        (denoteGraphDistributedFaithful pm initPM 9713) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1084 l12PmAdd9717
    15973 9713 9717 elemwiseAdd
    (by native_decide) l12res_pm_node_facts.2.2.1 ?_
    (l12res_nonempty_pm 1085) (l12res_pm_not_written 1085 9717 (by decide))
    (l12res_nonempty_pm 1084) (l12res_pm_not_written 1084 15973 (by decide))
    (l12res_pm_not_written 1084 9713 (by decide))
  intro s
  unfold l12PmAdd9717
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 15973 9713 9717

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12res_red_pm9718 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9718 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 15981)
        (denoteGraphDistributedFaithful pm initPM 9714) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1085 l12PmAdd9718
    15981 9714 9718 elemwiseAdd
    (by native_decide) l12res_pm_node_facts.2.2.2.1 ?_
    (l12res_nonempty_pm 1086) (l12res_pm_not_written 1086 9718 (by decide))
    (l12res_nonempty_pm 1085) (l12res_pm_not_written 1085 15981 (by decide))
    (l12res_pm_not_written 1085 9714 (by decide))
  intro s
  unfold l12PmAdd9718
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 15981 9714 9718

/-! ### The bypass relation -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Zigzag relation for the residual bypass tensor 8143 (PM 15973 / 15981),
-- stated against the `5345` cumulative-sequence metadata used downstream.
private theorem l12_8143_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8143)
      (denoteGraphDistributedFaithful pm initPM 15973)
      (denoteGraphDistributedFaithful pm initPM 15981)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have h38 := recon_zigzagGoal_5338_distributed initSM initPM hSM hPM hInit hCu
  have pmFinal (tid : Tid) (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hw
  have h5337_5345 : denoteGraphDistributedFaithful pm initPM 5337 =
      denoteGraphDistributedFaithful pm initPM 5345 := by
    rw [pmFinal 5337 (fun n hn => (l12res_cu_not_written n hn).1),
      pmFinal 5345 (fun n hn => (l12res_cu_not_written n hn).2)]
    exact TrainVerify.Denote.YOCInputValueClasses.pm_cuseq_q_5337_eq_5345 initPM
      hValues.2
  rw [l12res_red_sm8143 initSM, l12res_red_pm15973 initPM, l12res_red_pm15981 initPM,
    ← h5337_5345]
  exact h38

/-! ### Goals -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5353 (`FW_float` of 5352).
theorem recon_zigzagGoal_5353_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5353)
      (denoteGraphDistributedFaithful pm initPM 9713)
      (denoteGraphDistributedFaithful pm initPM 9714)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5352_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12res_red_sm5353 initSM, l12res_red_pm9713 initPM, l12res_red_pm9714 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5354 (residual `FW_add`).
theorem recon_zigzagGoal_5354_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5354)
      (denoteGraphDistributedFaithful pm initPM 9717)
      (denoteGraphDistributedFaithful pm initPM 9718)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hA := l12_8143_rel initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5353_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12res_red_sm5354 initSM, l12res_red_pm9717 initPM, l12res_red_pm9718 initPM]
  exact Zigzag2Rel.add 2048 1024 hA hB (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
