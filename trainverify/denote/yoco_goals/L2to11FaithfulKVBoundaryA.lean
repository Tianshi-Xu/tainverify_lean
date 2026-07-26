/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L12FaithfulReplicatedBoundary
import denote.yoco_goals.YOCInputValueClasses

/-!
# Entry-segment K-cache boundary casts for blocks 2-11

Structural clones of `recon_intermediateGoal_5343_faithful` /
`recon_intermediateGoal_5392_faithful`: the ten remaining `FW_to` casts of the
12-way fan-out of the global K projection `5334` (SM nodes 483-492, PM nodes
1038-1047), producing the replicated K-cache tensors 5441, 5490, 5539, 5588,
5637, 5686, 5735, 5784, 5833, 5882 (all of shape `[4096, 4, 64]`).

No new axioms, no new hypotheses: the parameter list is verbatim the one used by
the block-1 attention frontier.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option linter.unusedVariables false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

/-- `storeSet` over `l.zip (List.replicate m v)`: every tid occurring in `l` reads back
the constant value `v`, provided the replicate list is at least as long as `l`. -/
private theorem l2kv_storeSet_zip_replicate (s : Store) (v : Tensor) :
    ∀ (l : List Tid) (m : Nat) (t : Tid), t ∈ l → l.length ≤ m →
      storeSet s (l.zip (List.replicate m v)) t = v := by
  intro l
  induction l with
  | nil => intro m t ht _; cases ht
  | cons a l ih =>
    intro m t ht hlen
    match m with
    | 0 => simp at hlen
    | (m + 1) =>
      by_cases hat : a = t
      · subst hat
        rw [List.replicate_succ]
        change storeSet s ((a, v) :: (l.zip (List.replicate m v))) a = v
        unfold storeSet
        simp [List.find?]
      · have ht' : t ∈ l := by
          rcases List.mem_cons.mp ht with h | h
          · exact absurd h.symm hat
          · exact h
        have hlen' : l.length ≤ m := Nat.le_of_succ_le_succ hlen
        rw [List.replicate_succ]
        change storeSet s ((a, v) :: (l.zip (List.replicate m v))) t = v
        have hstep : storeSet s ((a, v) :: (l.zip (List.replicate m v))) t
            = storeSet s (l.zip (List.replicate m v)) t := by
          unfold storeSet
          simp [List.find?, hat]
        rw [hstep]
        exact ih m t ht' hlen'

/-- `applyNode` for an `n`-way `FW_multiref`: *every* output tid equals the input. -/
private theorem l2kv_applyNode_fw_multiref_out (g : GraphDecl) (s : Store) (rank n : Nat)
    (xTid : Tid) (outs : List Tid) (t : Tid) (hmem : t ∈ outs) (hlen : outs.length ≤ n) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := outs, params := [n] } t = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  exact l2kv_storeSet_zip_replicate s (s xTid) outs n t hmem hlen

private theorem l2kv_nonempty_sm (k : Nat) : ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l2kv_nonempty_pm (k : Nat) : ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l2kvA_sm_facts :
    sm.nodes[478]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] } ∧
    sm.nodes[483]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8041], outs := [5441] } ∧
    sm.nodes[484]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8045], outs := [5490] } ∧
    sm.nodes[485]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8049], outs := [5539] } ∧
    sm.nodes[486]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8053], outs := [5588] } ∧
    sm.nodes[487]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8057], outs := [5637] } ∧
    sm.nodes[488]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8061], outs := [5686] } ∧
    sm.nodes[489]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8065], outs := [5735] } ∧
    sm.nodes[490]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8069], outs := [5784] } ∧
    sm.nodes[491]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8073], outs := [5833] } ∧
    sm.nodes[492]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8077], outs := [5882] } := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l2kvA_pm_facts :
    pm.nodes[1021]'(by native_decide) =
      { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] } ∧
    pm.nodes[1038]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15823], outs := [5441] } ∧
    pm.nodes[1039]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15827], outs := [5490] } ∧
    pm.nodes[1040]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15831], outs := [5539] } ∧
    pm.nodes[1041]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15835], outs := [5588] } ∧
    pm.nodes[1042]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15839], outs := [5637] } ∧
    pm.nodes[1043]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15843], outs := [5686] } ∧
    pm.nodes[1044]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15847], outs := [5735] } ∧
    pm.nodes[1045]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15851], outs := [5784] } ∧
    pm.nodes[1046]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15855], outs := [5833] } ∧
    pm.nodes[1047]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15859], outs := [5882] } := by
  native_decide

private def l2kvASmPairs : List (Nat × Nat) :=
  [(479, 8041), (479, 8045), (479, 8049), (479, 8053), (479, 8057), (479, 8061), (479, 8065), (479, 8069), (479, 8073), (479, 8077), (478, 5334), (484, 5441), (483, 8041), (485, 5490), (484, 8045), (486, 5539), (485, 8049), (487, 5588), (486, 8053), (488, 5637), (487, 8057), (489, 5686), (488, 8061), (490, 5735), (489, 8065), (491, 5784), (490, 8069), (492, 5833), (491, 8073), (493, 5882), (492, 8077)]

private def l2kvAPmPairs : List (Nat × Nat) :=
  [(1022, 15823), (1022, 15827), (1022, 15831), (1022, 15835), (1022, 15839), (1022, 15843), (1022, 15847), (1022, 15851), (1022, 15855), (1022, 15859), (1021, 5334), (1039, 5441), (1038, 15823), (1040, 5490), (1039, 15827), (1041, 5539), (1040, 15831), (1042, 5588), (1041, 15835), (1043, 5637), (1042, 15839), (1044, 5686), (1043, 15843), (1045, 5735), (1044, 15847), (1046, 5784), (1045, 15851), (1047, 5833), (1046, 15855), (1048, 5882), (1047, 15859)]

set_option maxRecDepth 1000000 in
private theorem l2kvA_sm_not_written_all :
    ∀ p ∈ l2kvASmPairs, ∀ n ∈ sm.nodes.drop p.1, p.2 ∉ n.outs := by
  native_decide

private theorem l2kvA_sm_not_written (k tid : Nat) (h : (k, tid) ∈ l2kvASmPairs) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs :=
  l2kvA_sm_not_written_all (k, tid) h

set_option maxRecDepth 1000000 in
private theorem l2kvA_pm_not_written_all :
    ∀ p ∈ l2kvAPmPairs, ∀ n ∈ pm.nodes.drop p.1, p.2 ∉ n.outs := by
  native_decide

private theorem l2kvA_pm_not_written (k tid : Nat) (h : (k, tid) ∈ l2kvAPmPairs) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs :=
  l2kvA_pm_not_written_all (k, tid) h

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated K-cache cast 5441 (`FW_to` of fan-out 8041).
theorem recon_intermediateGoal_5441_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5441
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5334] using h
  rcases l2kvA_sm_facts with ⟨smr, sn483, _, _, _, _, _, _, _, _, _⟩
  rcases l2kvA_pm_facts with ⟨pmr, pn1038, _, _, _, _, _, _, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8041 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 478 _ 5334 8041 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8041 (by decide) (by decide))
      (l2kv_nonempty_sm 479) (l2kvA_sm_not_written 479 8041 (by decide))
      (l2kv_nonempty_sm 478) (l2kvA_sm_not_written 478 5334 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15823 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1021 _ 5334 15823 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15823 (by decide) (by decide))
      (l2kv_nonempty_pm 1022) (l2kvA_pm_not_written 1022 15823 (by decide))
      (l2kv_nonempty_pm 1021) (l2kvA_pm_not_written 1021 5334 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5441 =
      denoteGraphDistributedFaithful sm initSM 8041 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 483 _ 8041 5441 (fun x => x)
      (by native_decide) sn483 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8041 5441 [])
      (l2kv_nonempty_sm 484) (l2kvA_sm_not_written 484 5441 (by decide))
      (l2kv_nonempty_sm 483) (l2kvA_sm_not_written 483 8041 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5441 =
      denoteGraphDistributedFaithful pm initPM 15823 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1038 _ 15823 5441 (fun x => x)
      (by native_decide) pn1038 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15823 5441 [])
      (l2kv_nonempty_pm 1039) (l2kvA_pm_not_written 1039 5441 (by decide))
      (l2kv_nonempty_pm 1038) (l2kvA_pm_not_written 1038 15823 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5441 =
      denoteGraphDistributedFaithful pm initPM 5441 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5441).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5441 5441 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated K-cache cast 5490 (`FW_to` of fan-out 8045).
theorem recon_intermediateGoal_5490_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5490
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5334] using h
  rcases l2kvA_sm_facts with ⟨smr, _, sn484, _, _, _, _, _, _, _, _⟩
  rcases l2kvA_pm_facts with ⟨pmr, _, pn1039, _, _, _, _, _, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8045 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 478 _ 5334 8045 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8045 (by decide) (by decide))
      (l2kv_nonempty_sm 479) (l2kvA_sm_not_written 479 8045 (by decide))
      (l2kv_nonempty_sm 478) (l2kvA_sm_not_written 478 5334 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15827 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1021 _ 5334 15827 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15827 (by decide) (by decide))
      (l2kv_nonempty_pm 1022) (l2kvA_pm_not_written 1022 15827 (by decide))
      (l2kv_nonempty_pm 1021) (l2kvA_pm_not_written 1021 5334 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5490 =
      denoteGraphDistributedFaithful sm initSM 8045 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 484 _ 8045 5490 (fun x => x)
      (by native_decide) sn484 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8045 5490 [])
      (l2kv_nonempty_sm 485) (l2kvA_sm_not_written 485 5490 (by decide))
      (l2kv_nonempty_sm 484) (l2kvA_sm_not_written 484 8045 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5490 =
      denoteGraphDistributedFaithful pm initPM 15827 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1039 _ 15827 5490 (fun x => x)
      (by native_decide) pn1039 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15827 5490 [])
      (l2kv_nonempty_pm 1040) (l2kvA_pm_not_written 1040 5490 (by decide))
      (l2kv_nonempty_pm 1039) (l2kvA_pm_not_written 1039 15827 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5490 =
      denoteGraphDistributedFaithful pm initPM 5490 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5490).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5490 5490 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated K-cache cast 5539 (`FW_to` of fan-out 8049).
theorem recon_intermediateGoal_5539_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5539
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5334] using h
  rcases l2kvA_sm_facts with ⟨smr, _, _, sn485, _, _, _, _, _, _, _⟩
  rcases l2kvA_pm_facts with ⟨pmr, _, _, pn1040, _, _, _, _, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8049 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 478 _ 5334 8049 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8049 (by decide) (by decide))
      (l2kv_nonempty_sm 479) (l2kvA_sm_not_written 479 8049 (by decide))
      (l2kv_nonempty_sm 478) (l2kvA_sm_not_written 478 5334 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15831 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1021 _ 5334 15831 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15831 (by decide) (by decide))
      (l2kv_nonempty_pm 1022) (l2kvA_pm_not_written 1022 15831 (by decide))
      (l2kv_nonempty_pm 1021) (l2kvA_pm_not_written 1021 5334 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5539 =
      denoteGraphDistributedFaithful sm initSM 8049 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 485 _ 8049 5539 (fun x => x)
      (by native_decide) sn485 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8049 5539 [])
      (l2kv_nonempty_sm 486) (l2kvA_sm_not_written 486 5539 (by decide))
      (l2kv_nonempty_sm 485) (l2kvA_sm_not_written 485 8049 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5539 =
      denoteGraphDistributedFaithful pm initPM 15831 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1040 _ 15831 5539 (fun x => x)
      (by native_decide) pn1040 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15831 5539 [])
      (l2kv_nonempty_pm 1041) (l2kvA_pm_not_written 1041 5539 (by decide))
      (l2kv_nonempty_pm 1040) (l2kvA_pm_not_written 1040 15831 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5539 =
      denoteGraphDistributedFaithful pm initPM 5539 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5539).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5539 5539 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated K-cache cast 5588 (`FW_to` of fan-out 8053).
theorem recon_intermediateGoal_5588_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5588
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5334] using h
  rcases l2kvA_sm_facts with ⟨smr, _, _, _, sn486, _, _, _, _, _, _⟩
  rcases l2kvA_pm_facts with ⟨pmr, _, _, _, pn1041, _, _, _, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8053 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 478 _ 5334 8053 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8053 (by decide) (by decide))
      (l2kv_nonempty_sm 479) (l2kvA_sm_not_written 479 8053 (by decide))
      (l2kv_nonempty_sm 478) (l2kvA_sm_not_written 478 5334 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15835 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1021 _ 5334 15835 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15835 (by decide) (by decide))
      (l2kv_nonempty_pm 1022) (l2kvA_pm_not_written 1022 15835 (by decide))
      (l2kv_nonempty_pm 1021) (l2kvA_pm_not_written 1021 5334 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5588 =
      denoteGraphDistributedFaithful sm initSM 8053 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 486 _ 8053 5588 (fun x => x)
      (by native_decide) sn486 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8053 5588 [])
      (l2kv_nonempty_sm 487) (l2kvA_sm_not_written 487 5588 (by decide))
      (l2kv_nonempty_sm 486) (l2kvA_sm_not_written 486 8053 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5588 =
      denoteGraphDistributedFaithful pm initPM 15835 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1041 _ 15835 5588 (fun x => x)
      (by native_decide) pn1041 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15835 5588 [])
      (l2kv_nonempty_pm 1042) (l2kvA_pm_not_written 1042 5588 (by decide))
      (l2kv_nonempty_pm 1041) (l2kvA_pm_not_written 1041 15835 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5588 =
      denoteGraphDistributedFaithful pm initPM 5588 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5588).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5588 5588 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated K-cache cast 5637 (`FW_to` of fan-out 8057).
theorem recon_intermediateGoal_5637_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5637
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5334] using h
  rcases l2kvA_sm_facts with ⟨smr, _, _, _, _, sn487, _, _, _, _, _⟩
  rcases l2kvA_pm_facts with ⟨pmr, _, _, _, _, pn1042, _, _, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8057 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 478 _ 5334 8057 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8057 (by decide) (by decide))
      (l2kv_nonempty_sm 479) (l2kvA_sm_not_written 479 8057 (by decide))
      (l2kv_nonempty_sm 478) (l2kvA_sm_not_written 478 5334 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15839 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1021 _ 5334 15839 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15839 (by decide) (by decide))
      (l2kv_nonempty_pm 1022) (l2kvA_pm_not_written 1022 15839 (by decide))
      (l2kv_nonempty_pm 1021) (l2kvA_pm_not_written 1021 5334 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5637 =
      denoteGraphDistributedFaithful sm initSM 8057 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 487 _ 8057 5637 (fun x => x)
      (by native_decide) sn487 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8057 5637 [])
      (l2kv_nonempty_sm 488) (l2kvA_sm_not_written 488 5637 (by decide))
      (l2kv_nonempty_sm 487) (l2kvA_sm_not_written 487 8057 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5637 =
      denoteGraphDistributedFaithful pm initPM 15839 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1042 _ 15839 5637 (fun x => x)
      (by native_decide) pn1042 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15839 5637 [])
      (l2kv_nonempty_pm 1043) (l2kvA_pm_not_written 1043 5637 (by decide))
      (l2kv_nonempty_pm 1042) (l2kvA_pm_not_written 1042 15839 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5637 =
      denoteGraphDistributedFaithful pm initPM 5637 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5637).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5637 5637 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated K-cache cast 5686 (`FW_to` of fan-out 8061).
theorem recon_intermediateGoal_5686_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5686
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5334] using h
  rcases l2kvA_sm_facts with ⟨smr, _, _, _, _, _, sn488, _, _, _, _⟩
  rcases l2kvA_pm_facts with ⟨pmr, _, _, _, _, _, pn1043, _, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8061 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 478 _ 5334 8061 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8061 (by decide) (by decide))
      (l2kv_nonempty_sm 479) (l2kvA_sm_not_written 479 8061 (by decide))
      (l2kv_nonempty_sm 478) (l2kvA_sm_not_written 478 5334 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15843 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1021 _ 5334 15843 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15843 (by decide) (by decide))
      (l2kv_nonempty_pm 1022) (l2kvA_pm_not_written 1022 15843 (by decide))
      (l2kv_nonempty_pm 1021) (l2kvA_pm_not_written 1021 5334 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5686 =
      denoteGraphDistributedFaithful sm initSM 8061 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 488 _ 8061 5686 (fun x => x)
      (by native_decide) sn488 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8061 5686 [])
      (l2kv_nonempty_sm 489) (l2kvA_sm_not_written 489 5686 (by decide))
      (l2kv_nonempty_sm 488) (l2kvA_sm_not_written 488 8061 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5686 =
      denoteGraphDistributedFaithful pm initPM 15843 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1043 _ 15843 5686 (fun x => x)
      (by native_decide) pn1043 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15843 5686 [])
      (l2kv_nonempty_pm 1044) (l2kvA_pm_not_written 1044 5686 (by decide))
      (l2kv_nonempty_pm 1043) (l2kvA_pm_not_written 1043 15843 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5686 =
      denoteGraphDistributedFaithful pm initPM 5686 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5686).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5686 5686 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated K-cache cast 5735 (`FW_to` of fan-out 8065).
theorem recon_intermediateGoal_5735_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5735
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5334] using h
  rcases l2kvA_sm_facts with ⟨smr, _, _, _, _, _, _, sn489, _, _, _⟩
  rcases l2kvA_pm_facts with ⟨pmr, _, _, _, _, _, _, pn1044, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8065 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 478 _ 5334 8065 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8065 (by decide) (by decide))
      (l2kv_nonempty_sm 479) (l2kvA_sm_not_written 479 8065 (by decide))
      (l2kv_nonempty_sm 478) (l2kvA_sm_not_written 478 5334 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15847 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1021 _ 5334 15847 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15847 (by decide) (by decide))
      (l2kv_nonempty_pm 1022) (l2kvA_pm_not_written 1022 15847 (by decide))
      (l2kv_nonempty_pm 1021) (l2kvA_pm_not_written 1021 5334 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5735 =
      denoteGraphDistributedFaithful sm initSM 8065 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 489 _ 8065 5735 (fun x => x)
      (by native_decide) sn489 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8065 5735 [])
      (l2kv_nonempty_sm 490) (l2kvA_sm_not_written 490 5735 (by decide))
      (l2kv_nonempty_sm 489) (l2kvA_sm_not_written 489 8065 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5735 =
      denoteGraphDistributedFaithful pm initPM 15847 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1044 _ 15847 5735 (fun x => x)
      (by native_decide) pn1044 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15847 5735 [])
      (l2kv_nonempty_pm 1045) (l2kvA_pm_not_written 1045 5735 (by decide))
      (l2kv_nonempty_pm 1044) (l2kvA_pm_not_written 1044 15847 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5735 =
      denoteGraphDistributedFaithful pm initPM 5735 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5735).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5735 5735 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated K-cache cast 5784 (`FW_to` of fan-out 8069).
theorem recon_intermediateGoal_5784_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5784
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5334] using h
  rcases l2kvA_sm_facts with ⟨smr, _, _, _, _, _, _, _, sn490, _, _⟩
  rcases l2kvA_pm_facts with ⟨pmr, _, _, _, _, _, _, _, pn1045, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8069 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 478 _ 5334 8069 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8069 (by decide) (by decide))
      (l2kv_nonempty_sm 479) (l2kvA_sm_not_written 479 8069 (by decide))
      (l2kv_nonempty_sm 478) (l2kvA_sm_not_written 478 5334 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15851 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1021 _ 5334 15851 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15851 (by decide) (by decide))
      (l2kv_nonempty_pm 1022) (l2kvA_pm_not_written 1022 15851 (by decide))
      (l2kv_nonempty_pm 1021) (l2kvA_pm_not_written 1021 5334 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5784 =
      denoteGraphDistributedFaithful sm initSM 8069 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 490 _ 8069 5784 (fun x => x)
      (by native_decide) sn490 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8069 5784 [])
      (l2kv_nonempty_sm 491) (l2kvA_sm_not_written 491 5784 (by decide))
      (l2kv_nonempty_sm 490) (l2kvA_sm_not_written 490 8069 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5784 =
      denoteGraphDistributedFaithful pm initPM 15851 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1045 _ 15851 5784 (fun x => x)
      (by native_decide) pn1045 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15851 5784 [])
      (l2kv_nonempty_pm 1046) (l2kvA_pm_not_written 1046 5784 (by decide))
      (l2kv_nonempty_pm 1045) (l2kvA_pm_not_written 1045 15851 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5784 =
      denoteGraphDistributedFaithful pm initPM 5784 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5784).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5784 5784 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated K-cache cast 5833 (`FW_to` of fan-out 8073).
theorem recon_intermediateGoal_5833_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5833
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5334] using h
  rcases l2kvA_sm_facts with ⟨smr, _, _, _, _, _, _, _, _, sn491, _⟩
  rcases l2kvA_pm_facts with ⟨pmr, _, _, _, _, _, _, _, _, pn1046, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8073 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 478 _ 5334 8073 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8073 (by decide) (by decide))
      (l2kv_nonempty_sm 479) (l2kvA_sm_not_written 479 8073 (by decide))
      (l2kv_nonempty_sm 478) (l2kvA_sm_not_written 478 5334 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15855 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1021 _ 5334 15855 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15855 (by decide) (by decide))
      (l2kv_nonempty_pm 1022) (l2kvA_pm_not_written 1022 15855 (by decide))
      (l2kv_nonempty_pm 1021) (l2kvA_pm_not_written 1021 5334 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5833 =
      denoteGraphDistributedFaithful sm initSM 8073 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 491 _ 8073 5833 (fun x => x)
      (by native_decide) sn491 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8073 5833 [])
      (l2kv_nonempty_sm 492) (l2kvA_sm_not_written 492 5833 (by decide))
      (l2kv_nonempty_sm 491) (l2kvA_sm_not_written 491 8073 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5833 =
      denoteGraphDistributedFaithful pm initPM 15855 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1046 _ 15855 5833 (fun x => x)
      (by native_decide) pn1046 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15855 5833 [])
      (l2kv_nonempty_pm 1047) (l2kvA_pm_not_written 1047 5833 (by decide))
      (l2kv_nonempty_pm 1046) (l2kvA_pm_not_written 1046 15855 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5833 =
      denoteGraphDistributedFaithful pm initPM 5833 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5833).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5833 5833 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated K-cache cast 5882 (`FW_to` of fan-out 8077).
theorem recon_intermediateGoal_5882_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5882
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5334] using h
  rcases l2kvA_sm_facts with ⟨smr, _, _, _, _, _, _, _, _, _, sn492⟩
  rcases l2kvA_pm_facts with ⟨pmr, _, _, _, _, _, _, _, _, _, pn1047⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8077 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 478 _ 5334 8077 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8077 (by decide) (by decide))
      (l2kv_nonempty_sm 479) (l2kvA_sm_not_written 479 8077 (by decide))
      (l2kv_nonempty_sm 478) (l2kvA_sm_not_written 478 5334 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15859 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1021 _ 5334 15859 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15859 (by decide) (by decide))
      (l2kv_nonempty_pm 1022) (l2kvA_pm_not_written 1022 15859 (by decide))
      (l2kv_nonempty_pm 1021) (l2kvA_pm_not_written 1021 5334 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5882 =
      denoteGraphDistributedFaithful sm initSM 8077 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 492 _ 8077 5882 (fun x => x)
      (by native_decide) sn492 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8077 5882 [])
      (l2kv_nonempty_sm 493) (l2kvA_sm_not_written 493 5882 (by decide))
      (l2kv_nonempty_sm 492) (l2kvA_sm_not_written 492 8077 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5882 =
      denoteGraphDistributedFaithful pm initPM 15859 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1047 _ 15859 5882 (fun x => x)
      (by native_decide) pn1047 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15859 5882 [])
      (l2kv_nonempty_pm 1048) (l2kvA_pm_not_written 1048 5882 (by decide))
      (l2kv_nonempty_pm 1047) (l2kvA_pm_not_written 1047 15859 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5882 =
      denoteGraphDistributedFaithful pm initPM 5882 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5882).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5882 5882 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

end
end TrainVerify.Denote.GeneratedPatterns
