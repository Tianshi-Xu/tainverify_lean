/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L2to11FaithfulKVBoundaryA

/-!
# Entry-segment V-cache boundary casts for blocks 2-11

Structural clones of `recon_intermediateGoal_5344_faithful` /
`recon_intermediateGoal_5393_faithful`: the ten remaining `FW_to` casts of the
12-way fan-out of the global V projection `5336` (SM nodes 495-504, PM nodes
1062-1071), producing the replicated V-cache tensors 5442, 5491, 5540, 5589,
5638, 5687, 5736, 5785, 5834, 5883 (all of shape `[4096, 4, 64]`).
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
private theorem l2kvB_sm_facts :
    sm.nodes[479]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] } ∧
    sm.nodes[495]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8099], outs := [5442] } ∧
    sm.nodes[496]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8103], outs := [5491] } ∧
    sm.nodes[497]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8107], outs := [5540] } ∧
    sm.nodes[498]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8111], outs := [5589] } ∧
    sm.nodes[499]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8115], outs := [5638] } ∧
    sm.nodes[500]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8119], outs := [5687] } ∧
    sm.nodes[501]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8123], outs := [5736] } ∧
    sm.nodes[502]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8127], outs := [5785] } ∧
    sm.nodes[503]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8131], outs := [5834] } ∧
    sm.nodes[504]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8135], outs := [5883] } := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l2kvB_pm_facts :
    pm.nodes[1023]'(by native_decide) =
      { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] } ∧
    pm.nodes[1062]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15929], outs := [5442] } ∧
    pm.nodes[1063]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15933], outs := [5491] } ∧
    pm.nodes[1064]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15937], outs := [5540] } ∧
    pm.nodes[1065]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15941], outs := [5589] } ∧
    pm.nodes[1066]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15945], outs := [5638] } ∧
    pm.nodes[1067]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15949], outs := [5687] } ∧
    pm.nodes[1068]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15953], outs := [5736] } ∧
    pm.nodes[1069]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15957], outs := [5785] } ∧
    pm.nodes[1070]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15961], outs := [5834] } ∧
    pm.nodes[1071]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15965], outs := [5883] } := by
  native_decide

private def l2kvBSmPairs : List (Nat × Nat) :=
  [(480, 8099), (480, 8103), (480, 8107), (480, 8111), (480, 8115), (480, 8119), (480, 8123), (480, 8127), (480, 8131), (480, 8135), (479, 5336), (496, 5442), (495, 8099), (497, 5491), (496, 8103), (498, 5540), (497, 8107), (499, 5589), (498, 8111), (500, 5638), (499, 8115), (501, 5687), (500, 8119), (502, 5736), (501, 8123), (503, 5785), (502, 8127), (504, 5834), (503, 8131), (505, 5883), (504, 8135)]

private def l2kvBPmPairs : List (Nat × Nat) :=
  [(1024, 15929), (1024, 15933), (1024, 15937), (1024, 15941), (1024, 15945), (1024, 15949), (1024, 15953), (1024, 15957), (1024, 15961), (1024, 15965), (1023, 5336), (1063, 5442), (1062, 15929), (1064, 5491), (1063, 15933), (1065, 5540), (1064, 15937), (1066, 5589), (1065, 15941), (1067, 5638), (1066, 15945), (1068, 5687), (1067, 15949), (1069, 5736), (1068, 15953), (1070, 5785), (1069, 15957), (1071, 5834), (1070, 15961), (1072, 5883), (1071, 15965)]

set_option maxRecDepth 1000000 in
private theorem l2kvB_sm_not_written_all :
    ∀ p ∈ l2kvBSmPairs, ∀ n ∈ sm.nodes.drop p.1, p.2 ∉ n.outs := by
  native_decide

private theorem l2kvB_sm_not_written (k tid : Nat) (h : (k, tid) ∈ l2kvBSmPairs) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs :=
  l2kvB_sm_not_written_all (k, tid) h

set_option maxRecDepth 1000000 in
private theorem l2kvB_pm_not_written_all :
    ∀ p ∈ l2kvBPmPairs, ∀ n ∈ pm.nodes.drop p.1, p.2 ∉ n.outs := by
  native_decide

private theorem l2kvB_pm_not_written (k tid : Nat) (h : (k, tid) ∈ l2kvBPmPairs) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs :=
  l2kvB_pm_not_written_all (k, tid) h

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated V-cache cast 5442 (`FW_to` of fan-out 8099).
theorem recon_intermediateGoal_5442_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5442
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5336] using h
  rcases l2kvB_sm_facts with ⟨smr, sn495, _, _, _, _, _, _, _, _, _⟩
  rcases l2kvB_pm_facts with ⟨pmr, pn1062, _, _, _, _, _, _, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8099 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 479 _ 5336 8099 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8099 (by decide) (by decide))
      (l2kv_nonempty_sm 480) (l2kvB_sm_not_written 480 8099 (by decide))
      (l2kv_nonempty_sm 479) (l2kvB_sm_not_written 479 5336 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15929 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1023 _ 5336 15929 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15929 (by decide) (by decide))
      (l2kv_nonempty_pm 1024) (l2kvB_pm_not_written 1024 15929 (by decide))
      (l2kv_nonempty_pm 1023) (l2kvB_pm_not_written 1023 5336 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5442 =
      denoteGraphDistributedFaithful sm initSM 8099 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 495 _ 8099 5442 (fun x => x)
      (by native_decide) sn495 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8099 5442 [])
      (l2kv_nonempty_sm 496) (l2kvB_sm_not_written 496 5442 (by decide))
      (l2kv_nonempty_sm 495) (l2kvB_sm_not_written 495 8099 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5442 =
      denoteGraphDistributedFaithful pm initPM 15929 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1062 _ 15929 5442 (fun x => x)
      (by native_decide) pn1062 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15929 5442 [])
      (l2kv_nonempty_pm 1063) (l2kvB_pm_not_written 1063 5442 (by decide))
      (l2kv_nonempty_pm 1062) (l2kvB_pm_not_written 1062 15929 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5442 =
      denoteGraphDistributedFaithful pm initPM 5442 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5442).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5442 5442 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated V-cache cast 5491 (`FW_to` of fan-out 8103).
theorem recon_intermediateGoal_5491_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5491
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5336] using h
  rcases l2kvB_sm_facts with ⟨smr, _, sn496, _, _, _, _, _, _, _, _⟩
  rcases l2kvB_pm_facts with ⟨pmr, _, pn1063, _, _, _, _, _, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8103 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 479 _ 5336 8103 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8103 (by decide) (by decide))
      (l2kv_nonempty_sm 480) (l2kvB_sm_not_written 480 8103 (by decide))
      (l2kv_nonempty_sm 479) (l2kvB_sm_not_written 479 5336 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15933 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1023 _ 5336 15933 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15933 (by decide) (by decide))
      (l2kv_nonempty_pm 1024) (l2kvB_pm_not_written 1024 15933 (by decide))
      (l2kv_nonempty_pm 1023) (l2kvB_pm_not_written 1023 5336 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5491 =
      denoteGraphDistributedFaithful sm initSM 8103 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 496 _ 8103 5491 (fun x => x)
      (by native_decide) sn496 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8103 5491 [])
      (l2kv_nonempty_sm 497) (l2kvB_sm_not_written 497 5491 (by decide))
      (l2kv_nonempty_sm 496) (l2kvB_sm_not_written 496 8103 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5491 =
      denoteGraphDistributedFaithful pm initPM 15933 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1063 _ 15933 5491 (fun x => x)
      (by native_decide) pn1063 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15933 5491 [])
      (l2kv_nonempty_pm 1064) (l2kvB_pm_not_written 1064 5491 (by decide))
      (l2kv_nonempty_pm 1063) (l2kvB_pm_not_written 1063 15933 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5491 =
      denoteGraphDistributedFaithful pm initPM 5491 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5491).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5491 5491 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated V-cache cast 5540 (`FW_to` of fan-out 8107).
theorem recon_intermediateGoal_5540_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5540
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5336] using h
  rcases l2kvB_sm_facts with ⟨smr, _, _, sn497, _, _, _, _, _, _, _⟩
  rcases l2kvB_pm_facts with ⟨pmr, _, _, pn1064, _, _, _, _, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8107 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 479 _ 5336 8107 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8107 (by decide) (by decide))
      (l2kv_nonempty_sm 480) (l2kvB_sm_not_written 480 8107 (by decide))
      (l2kv_nonempty_sm 479) (l2kvB_sm_not_written 479 5336 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15937 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1023 _ 5336 15937 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15937 (by decide) (by decide))
      (l2kv_nonempty_pm 1024) (l2kvB_pm_not_written 1024 15937 (by decide))
      (l2kv_nonempty_pm 1023) (l2kvB_pm_not_written 1023 5336 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5540 =
      denoteGraphDistributedFaithful sm initSM 8107 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 497 _ 8107 5540 (fun x => x)
      (by native_decide) sn497 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8107 5540 [])
      (l2kv_nonempty_sm 498) (l2kvB_sm_not_written 498 5540 (by decide))
      (l2kv_nonempty_sm 497) (l2kvB_sm_not_written 497 8107 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5540 =
      denoteGraphDistributedFaithful pm initPM 15937 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1064 _ 15937 5540 (fun x => x)
      (by native_decide) pn1064 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15937 5540 [])
      (l2kv_nonempty_pm 1065) (l2kvB_pm_not_written 1065 5540 (by decide))
      (l2kv_nonempty_pm 1064) (l2kvB_pm_not_written 1064 15937 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5540 =
      denoteGraphDistributedFaithful pm initPM 5540 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5540).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5540 5540 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated V-cache cast 5589 (`FW_to` of fan-out 8111).
theorem recon_intermediateGoal_5589_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5589
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5336] using h
  rcases l2kvB_sm_facts with ⟨smr, _, _, _, sn498, _, _, _, _, _, _⟩
  rcases l2kvB_pm_facts with ⟨pmr, _, _, _, pn1065, _, _, _, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8111 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 479 _ 5336 8111 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8111 (by decide) (by decide))
      (l2kv_nonempty_sm 480) (l2kvB_sm_not_written 480 8111 (by decide))
      (l2kv_nonempty_sm 479) (l2kvB_sm_not_written 479 5336 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15941 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1023 _ 5336 15941 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15941 (by decide) (by decide))
      (l2kv_nonempty_pm 1024) (l2kvB_pm_not_written 1024 15941 (by decide))
      (l2kv_nonempty_pm 1023) (l2kvB_pm_not_written 1023 5336 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5589 =
      denoteGraphDistributedFaithful sm initSM 8111 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 498 _ 8111 5589 (fun x => x)
      (by native_decide) sn498 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8111 5589 [])
      (l2kv_nonempty_sm 499) (l2kvB_sm_not_written 499 5589 (by decide))
      (l2kv_nonempty_sm 498) (l2kvB_sm_not_written 498 8111 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5589 =
      denoteGraphDistributedFaithful pm initPM 15941 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1065 _ 15941 5589 (fun x => x)
      (by native_decide) pn1065 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15941 5589 [])
      (l2kv_nonempty_pm 1066) (l2kvB_pm_not_written 1066 5589 (by decide))
      (l2kv_nonempty_pm 1065) (l2kvB_pm_not_written 1065 15941 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5589 =
      denoteGraphDistributedFaithful pm initPM 5589 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5589).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5589 5589 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated V-cache cast 5638 (`FW_to` of fan-out 8115).
theorem recon_intermediateGoal_5638_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5638
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5336] using h
  rcases l2kvB_sm_facts with ⟨smr, _, _, _, _, sn499, _, _, _, _, _⟩
  rcases l2kvB_pm_facts with ⟨pmr, _, _, _, _, pn1066, _, _, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8115 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 479 _ 5336 8115 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8115 (by decide) (by decide))
      (l2kv_nonempty_sm 480) (l2kvB_sm_not_written 480 8115 (by decide))
      (l2kv_nonempty_sm 479) (l2kvB_sm_not_written 479 5336 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15945 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1023 _ 5336 15945 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15945 (by decide) (by decide))
      (l2kv_nonempty_pm 1024) (l2kvB_pm_not_written 1024 15945 (by decide))
      (l2kv_nonempty_pm 1023) (l2kvB_pm_not_written 1023 5336 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5638 =
      denoteGraphDistributedFaithful sm initSM 8115 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 499 _ 8115 5638 (fun x => x)
      (by native_decide) sn499 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8115 5638 [])
      (l2kv_nonempty_sm 500) (l2kvB_sm_not_written 500 5638 (by decide))
      (l2kv_nonempty_sm 499) (l2kvB_sm_not_written 499 8115 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5638 =
      denoteGraphDistributedFaithful pm initPM 15945 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1066 _ 15945 5638 (fun x => x)
      (by native_decide) pn1066 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15945 5638 [])
      (l2kv_nonempty_pm 1067) (l2kvB_pm_not_written 1067 5638 (by decide))
      (l2kv_nonempty_pm 1066) (l2kvB_pm_not_written 1066 15945 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5638 =
      denoteGraphDistributedFaithful pm initPM 5638 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5638).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5638 5638 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated V-cache cast 5687 (`FW_to` of fan-out 8119).
theorem recon_intermediateGoal_5687_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5687
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5336] using h
  rcases l2kvB_sm_facts with ⟨smr, _, _, _, _, _, sn500, _, _, _, _⟩
  rcases l2kvB_pm_facts with ⟨pmr, _, _, _, _, _, pn1067, _, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8119 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 479 _ 5336 8119 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8119 (by decide) (by decide))
      (l2kv_nonempty_sm 480) (l2kvB_sm_not_written 480 8119 (by decide))
      (l2kv_nonempty_sm 479) (l2kvB_sm_not_written 479 5336 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15949 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1023 _ 5336 15949 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15949 (by decide) (by decide))
      (l2kv_nonempty_pm 1024) (l2kvB_pm_not_written 1024 15949 (by decide))
      (l2kv_nonempty_pm 1023) (l2kvB_pm_not_written 1023 5336 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5687 =
      denoteGraphDistributedFaithful sm initSM 8119 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 500 _ 8119 5687 (fun x => x)
      (by native_decide) sn500 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8119 5687 [])
      (l2kv_nonempty_sm 501) (l2kvB_sm_not_written 501 5687 (by decide))
      (l2kv_nonempty_sm 500) (l2kvB_sm_not_written 500 8119 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5687 =
      denoteGraphDistributedFaithful pm initPM 15949 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1067 _ 15949 5687 (fun x => x)
      (by native_decide) pn1067 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15949 5687 [])
      (l2kv_nonempty_pm 1068) (l2kvB_pm_not_written 1068 5687 (by decide))
      (l2kv_nonempty_pm 1067) (l2kvB_pm_not_written 1067 15949 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5687 =
      denoteGraphDistributedFaithful pm initPM 5687 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5687).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5687 5687 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated V-cache cast 5736 (`FW_to` of fan-out 8123).
theorem recon_intermediateGoal_5736_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5736
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5336] using h
  rcases l2kvB_sm_facts with ⟨smr, _, _, _, _, _, _, sn501, _, _, _⟩
  rcases l2kvB_pm_facts with ⟨pmr, _, _, _, _, _, _, pn1068, _, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8123 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 479 _ 5336 8123 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8123 (by decide) (by decide))
      (l2kv_nonempty_sm 480) (l2kvB_sm_not_written 480 8123 (by decide))
      (l2kv_nonempty_sm 479) (l2kvB_sm_not_written 479 5336 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15953 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1023 _ 5336 15953 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15953 (by decide) (by decide))
      (l2kv_nonempty_pm 1024) (l2kvB_pm_not_written 1024 15953 (by decide))
      (l2kv_nonempty_pm 1023) (l2kvB_pm_not_written 1023 5336 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5736 =
      denoteGraphDistributedFaithful sm initSM 8123 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 501 _ 8123 5736 (fun x => x)
      (by native_decide) sn501 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8123 5736 [])
      (l2kv_nonempty_sm 502) (l2kvB_sm_not_written 502 5736 (by decide))
      (l2kv_nonempty_sm 501) (l2kvB_sm_not_written 501 8123 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5736 =
      denoteGraphDistributedFaithful pm initPM 15953 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1068 _ 15953 5736 (fun x => x)
      (by native_decide) pn1068 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15953 5736 [])
      (l2kv_nonempty_pm 1069) (l2kvB_pm_not_written 1069 5736 (by decide))
      (l2kv_nonempty_pm 1068) (l2kvB_pm_not_written 1068 15953 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5736 =
      denoteGraphDistributedFaithful pm initPM 5736 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5736).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5736 5736 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated V-cache cast 5785 (`FW_to` of fan-out 8127).
theorem recon_intermediateGoal_5785_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5785
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5336] using h
  rcases l2kvB_sm_facts with ⟨smr, _, _, _, _, _, _, _, sn502, _, _⟩
  rcases l2kvB_pm_facts with ⟨pmr, _, _, _, _, _, _, _, pn1069, _, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8127 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 479 _ 5336 8127 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8127 (by decide) (by decide))
      (l2kv_nonempty_sm 480) (l2kvB_sm_not_written 480 8127 (by decide))
      (l2kv_nonempty_sm 479) (l2kvB_sm_not_written 479 5336 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15957 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1023 _ 5336 15957 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15957 (by decide) (by decide))
      (l2kv_nonempty_pm 1024) (l2kvB_pm_not_written 1024 15957 (by decide))
      (l2kv_nonempty_pm 1023) (l2kvB_pm_not_written 1023 5336 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5785 =
      denoteGraphDistributedFaithful sm initSM 8127 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 502 _ 8127 5785 (fun x => x)
      (by native_decide) sn502 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8127 5785 [])
      (l2kv_nonempty_sm 503) (l2kvB_sm_not_written 503 5785 (by decide))
      (l2kv_nonempty_sm 502) (l2kvB_sm_not_written 502 8127 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5785 =
      denoteGraphDistributedFaithful pm initPM 15957 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1069 _ 15957 5785 (fun x => x)
      (by native_decide) pn1069 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15957 5785 [])
      (l2kv_nonempty_pm 1070) (l2kvB_pm_not_written 1070 5785 (by decide))
      (l2kv_nonempty_pm 1069) (l2kvB_pm_not_written 1069 15957 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5785 =
      denoteGraphDistributedFaithful pm initPM 5785 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5785).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5785 5785 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated V-cache cast 5834 (`FW_to` of fan-out 8131).
theorem recon_intermediateGoal_5834_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5834
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5336] using h
  rcases l2kvB_sm_facts with ⟨smr, _, _, _, _, _, _, _, _, sn503, _⟩
  rcases l2kvB_pm_facts with ⟨pmr, _, _, _, _, _, _, _, _, pn1070, _⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8131 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 479 _ 5336 8131 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8131 (by decide) (by decide))
      (l2kv_nonempty_sm 480) (l2kvB_sm_not_written 480 8131 (by decide))
      (l2kv_nonempty_sm 479) (l2kvB_sm_not_written 479 5336 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15961 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1023 _ 5336 15961 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15961 (by decide) (by decide))
      (l2kv_nonempty_pm 1024) (l2kvB_pm_not_written 1024 15961 (by decide))
      (l2kv_nonempty_pm 1023) (l2kvB_pm_not_written 1023 5336 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5834 =
      denoteGraphDistributedFaithful sm initSM 8131 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 503 _ 8131 5834 (fun x => x)
      (by native_decide) sn503 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8131 5834 [])
      (l2kv_nonempty_sm 504) (l2kvB_sm_not_written 504 5834 (by decide))
      (l2kv_nonempty_sm 503) (l2kvB_sm_not_written 503 8131 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5834 =
      denoteGraphDistributedFaithful pm initPM 15961 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1070 _ 15961 5834 (fun x => x)
      (by native_decide) pn1070 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15961 5834 [])
      (l2kv_nonempty_pm 1071) (l2kvB_pm_not_written 1071 5834 (by decide))
      (l2kv_nonempty_pm 1070) (l2kvB_pm_not_written 1070 15961 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5834 =
      denoteGraphDistributedFaithful pm initPM 5834 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5834).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5834 5834 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- Faithful replicated V-cache cast 5883 (`FW_to` of fan-out 8135).
theorem recon_intermediateGoal_5883_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5883
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsrc := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hvsrc := oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hsrc
  have hssrc : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hsrc.1
    simpa [intermediateGoal_5336] using h
  rcases l2kvB_sm_facts with ⟨smr, _, _, _, _, _, _, _, _, _, sn504⟩
  rcases l2kvB_pm_facts with ⟨pmr, _, _, _, _, _, _, _, _, _, pn1071⟩
  have sfan : denoteGraphDistributedFaithful sm initSM 8135 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 479 _ 5336 8135 (fun x => x)
      (by native_decide) smr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out sm s 0 12 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8135 (by decide) (by decide))
      (l2kv_nonempty_sm 480) (l2kvB_sm_not_written 480 8135 (by decide))
      (l2kv_nonempty_sm 479) (l2kvB_sm_not_written 479 5336 (by decide))
  have pfan : denoteGraphDistributedFaithful pm initPM 15965 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1023 _ 5336 15965 (fun x => x)
      (by native_decide) pmr (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l2kv_applyNode_fw_multiref_out pm s 1 12 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15965 (by decide) (by decide))
      (l2kv_nonempty_pm 1024) (l2kvB_pm_not_written 1024 15965 (by decide))
      (l2kv_nonempty_pm 1023) (l2kvB_pm_not_written 1023 5336 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5883 =
      denoteGraphDistributedFaithful sm initSM 8135 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 504 _ 8135 5883 (fun x => x)
      (by native_decide) sn504 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8135 5883 [])
      (l2kv_nonempty_sm 505) (l2kvB_sm_not_written 505 5883 (by decide))
      (l2kv_nonempty_sm 504) (l2kvB_sm_not_written 504 8135 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5883 =
      denoteGraphDistributedFaithful pm initPM 15965 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1071 _ 15965 5883 (fun x => x)
      (by native_decide) pn1071 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15965 5883 [])
      (l2kv_nonempty_pm 1072) (l2kvB_pm_not_written 1072 5883 (by decide))
      (l2kv_nonempty_pm 1071) (l2kvB_pm_not_written 1071 15965 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5883 =
      denoteGraphDistributedFaithful pm initPM 5883 := by
    rw [rSM, rPM, sfan, pfan, hvsrc]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5883).shape = [4096, 4, 64] := by
    rw [rSM, sfan]
    exact hssrc
  exact wrap_1tp_gen _ _ intermediateGoal_5883 5883 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

end
end TrainVerify.Denote.GeneratedPatterns
