import denote.yoco_goals.L12FaithfulReplicatedBoundary
import denote.yoco_goals.YOCInputValueClasses

/-!
# Block 1 faithful replicated K/V boundary

Structural clone of `L12FaithfulReplicatedBoundary`'s
`recon_intermediateGoal_5343_faithful` / `_5344_faithful`, shifted to the second
decoder block's K/V cache casts:

* `recon_intermediateGoal_5392_faithful` — `FW_to` of the *second* fan-out of the
  global K projection `5334` (SM node 482, PM node 1037), shape `[4096, 4, 64]`.
* `recon_intermediateGoal_5393_faithful` — `FW_to` of the *second* fan-out of the
  global V projection `5336` (SM node 494, PM node 1061), shape `[4096, 4, 64]`.

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

/-- `applyNode` for a `FW_multiref` with `outs = t1 :: t2 :: rest` and
`params = [n+2]`: the *second* output equals the input (when `t1 ≠ t2`). -/
private theorem l13_applyNode_fw_multiref_second_out (g : GraphDecl) (s : Store) (rank n : Nat)
    (xTid t1 t2 : Tid) (rest : List Tid) (hne : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := t1 :: t2 :: rest, params := [n + 2] } t2 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ((t1 :: t2 :: rest).zip (List.replicate (n + 2) (s xTid))) t2 = _
  unfold storeSet
  simp [List.replicate_succ, List.zip, List.zipWith, List.find?, hne]

set_option maxRecDepth 1000000 in
private theorem l13_fw_to_sm_facts :
    sm.nodes[478]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [5334],
        outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] } ∧
    sm.nodes[482]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8037], outs := [5392] } ∧
    sm.nodes[479]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [5336],
        outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] } ∧
    sm.nodes[494]'(by native_decide) =
      { rank := 0, op := "OpName.FW_to", ins := [8095], outs := [5393] } := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l13_fw_to_pm_facts :
    pm.nodes[1021]'(by native_decide) =
      { rank := 1, op := "OpName.FW_multiref", ins := [5334],
        outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] } ∧
    pm.nodes[1037]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15819], outs := [5392] } ∧
    pm.nodes[1023]'(by native_decide) =
      { rank := 1, op := "OpName.FW_multiref", ins := [5336],
        outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] } ∧
    pm.nodes[1061]'(by native_decide) =
      { rank := 1, op := "OpName.FW_to", ins := [15925], outs := [5393] } := by
  native_decide

private theorem l13_fw_to_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈
      [(479, 8037), (478, 5334), (483, 5392), (482, 8037),
       (480, 8095), (479, 5336), (495, 5393), (494, 8095)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem l13_fw_to_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈
      [(1022, 15819), (1021, 5334), (1038, 5392), (1037, 15819),
       (1024, 15925), (1023, 5336), (1062, 5393), (1061, 15925)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem l13_faithful_nonempty_sm (k : Nat) : ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l13_faithful_nonempty_pm (k : Nat) : ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful replicated block-1 K-cache cast from the global K projection. -/
theorem recon_intermediateGoal_5392_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5392
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have h34 := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hv34 := oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl h34
  have hs34 : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have h := h34.1
    simpa [intermediateGoal_5334] using h
  rcases l13_fw_to_sm_facts with ⟨sn478, sn482, _, _⟩
  rcases l13_fw_to_pm_facts with ⟨pn1021, pn1037, _, _⟩
  have s8037 : denoteGraphDistributedFaithful sm initSM 8037 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 478 _ 5334 8037 (fun x => x)
      (by native_decide) sn478 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l13_applyNode_fw_multiref_second_out sm s 0 10 5334 8033 8037
          [8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] (by decide))
      (l13_faithful_nonempty_sm 479) (l13_fw_to_sm_not_written 479 8037 (by decide))
      (l13_faithful_nonempty_sm 478) (l13_fw_to_sm_not_written 478 5334 (by decide))
  have p15819 : denoteGraphDistributedFaithful pm initPM 15819 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1021 _ 5334 15819 (fun x => x)
      (by native_decide) pn1021 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l13_applyNode_fw_multiref_second_out pm s 1 10 5334 15815 15819
          [15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] (by decide))
      (l13_faithful_nonempty_pm 1022) (l13_fw_to_pm_not_written 1022 15819 (by decide))
      (l13_faithful_nonempty_pm 1021) (l13_fw_to_pm_not_written 1021 5334 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5392 =
      denoteGraphDistributedFaithful sm initSM 8037 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 482 _ 8037 5392 (fun x => x)
      (by native_decide) sn482 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8037 5392 [])
      (l13_faithful_nonempty_sm 483) (l13_fw_to_sm_not_written 483 5392 (by decide))
      (l13_faithful_nonempty_sm 482) (l13_fw_to_sm_not_written 482 8037 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5392 =
      denoteGraphDistributedFaithful pm initPM 15819 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1037 _ 15819 5392 (fun x => x)
      (by native_decide) pn1037 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15819 5392 [])
      (l13_faithful_nonempty_pm 1038) (l13_fw_to_pm_not_written 1038 5392 (by decide))
      (l13_faithful_nonempty_pm 1037) (l13_fw_to_pm_not_written 1037 15819 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5392 =
      denoteGraphDistributedFaithful pm initPM 5392 := by
    rw [rSM, rPM, s8037, p15819, hv34]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5392).shape = [4096, 4, 64] := by
    rw [rSM, s8037]
    exact hs34
  exact wrap_1tp_gen _ _ intermediateGoal_5392 5392 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful replicated block-1 V-cache cast from the global V projection. -/
theorem recon_intermediateGoal_5393_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_5393
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have h36 := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hv36 := oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl h36
  have hs36 : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have h := h36.1
    simpa [intermediateGoal_5336] using h
  rcases l13_fw_to_sm_facts with ⟨_, _, sn479, sn494⟩
  rcases l13_fw_to_pm_facts with ⟨_, _, pn1023, pn1061⟩
  have s8095 : denoteGraphDistributedFaithful sm initSM 8095 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 479 _ 5336 8095 (fun x => x)
      (by native_decide) sn479 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l13_applyNode_fw_multiref_second_out sm s 0 10 5336 8091 8095
          [8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] (by decide))
      (l13_faithful_nonempty_sm 480) (l13_fw_to_sm_not_written 480 8095 (by decide))
      (l13_faithful_nonempty_sm 479) (l13_fw_to_sm_not_written 479 5336 (by decide))
  have p15925 : denoteGraphDistributedFaithful pm initPM 15925 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1023 _ 5336 15925 (fun x => x)
      (by native_decide) pn1023 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact l13_applyNode_fw_multiref_second_out pm s 1 10 5336 15921 15925
          [15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] (by decide))
      (l13_faithful_nonempty_pm 1024) (l13_fw_to_pm_not_written 1024 15925 (by decide))
      (l13_faithful_nonempty_pm 1023) (l13_fw_to_pm_not_written 1023 5336 (by decide))
  have rSM : denoteGraphDistributedFaithful sm initSM 5393 =
      denoteGraphDistributedFaithful sm initSM 8095 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 494 _ 8095 5393 (fun x => x)
      (by native_decide) sn494 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out sm s 0 8095 5393 [])
      (l13_faithful_nonempty_sm 495) (l13_fw_to_sm_not_written 495 5393 (by decide))
      (l13_faithful_nonempty_sm 494) (l13_fw_to_sm_not_written 494 8095 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5393 =
      denoteGraphDistributedFaithful pm initPM 15925 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1061 _ 15925 5393 (fun x => x)
      (by native_decide) pn1061 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_to_out pm s 1 15925 5393 [])
      (l13_faithful_nonempty_pm 1062) (l13_fw_to_pm_not_written 1062 5393 (by decide))
      (l13_faithful_nonempty_pm 1061) (l13_fw_to_pm_not_written 1061 15925 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5393 =
      denoteGraphDistributedFaithful pm initPM 5393 := by
    rw [rSM, rPM, s8095, p15925, hv36]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5393).shape = [4096, 4, 64] := by
    rw [rSM, s8095]
    exact hs36
  exact wrap_1tp_gen _ _ intermediateGoal_5393 5393 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

end
end TrainVerify.Denote.GeneratedPatterns
