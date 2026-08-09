/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.PackedCuSeqlensWitness
import denote.yoco_goals.Goal_1
import denote.yoco_goals.JointWitnessCore

/-!
# Joint witness for the Goal 1 public external contract

The stores below use the generated full-init shape tables.  Every shape `[2]`
input is assigned the concrete packed cumulative-sequence tensor `[0, 4096]`;
all other inputs are zero tensors of their generated shape.  Pinning every
`[2]` input (rather than only TID 6252) preserves the generated input value
classes and the full init-goal reconstruction equalities.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.JointWitness
open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedGoals
noncomputable section

private def lookupGeneratedShape (xs : List (Tid × Shape)) (tid : Tid) : Shape :=
  match xs.find? (fun p => p.1 = tid) with
  | some (_, sh) => sh
  | none => []

private def goal1SMShape : Tid → Shape := lookupGeneratedShape smInitShapes
private def goal1PMShape : Tid → Shape := lookupGeneratedShape pmInitShapes

private def isGoal1Packed (tid : Tid) : Bool :=
  decide (goal1SMShape tid = [2] ∧ goal1PMShape tid = [2])

private def goal1WitnessStore (shapeOf : Tid → Shape) : Store :=
  pinnedStore isGoal1Packed (packedCuSeqlensSingle 4096) shapeOf

private theorem goal1WitnessStore_shape (shapeOf : Tid → Shape)
    (hpinShape : ∀ tid, isGoal1Packed tid = true → shapeOf tid = [2])
    (tid : Tid) : (goal1WitnessStore shapeOf tid).shape = shapeOf tid := by
  unfold goal1WitnessStore
  by_cases h : isGoal1Packed tid = true
  · rw [pinnedStore_at_pin tid h, packedCuSeqlensSingle_shape, hpinShape tid h]
  · have hf : isGoal1Packed tid = false := by
      cases hx : isGoal1Packed tid <;> simp_all
    rw [pinnedStore_at_nonpin tid hf]
    rfl

private theorem goal1WitnessStore_shapes_hold_of_list
    (shapeOf : Tid → Shape) (xs : List (Tid × Shape))
    (hpinShape : ∀ tid, isGoal1Packed tid = true → shapeOf tid = [2])
    (h : xs.all (fun p => decide (shapeOf p.1 = p.2)) = true) :
    StoreShapesHold (goal1WitnessStore shapeOf) (shapeEnvOfList xs) := by
  have hz := zeroStore_shapes_hold_of_list (shapeOf := shapeOf) (xs := xs) h
  intro tid sh henv
  rw [goal1WitnessStore_shape shapeOf hpinShape]
  have hz' := hz tid sh henv
  rw [zeroStore_shape] at hz'
  exact hz'

private theorem goal1WitnessStore_eq
    (shapeOf : Tid → Shape) {a b : Tid}
    (hpin : isGoal1Packed a = isGoal1Packed b)
    (hshape : shapeOf a = shapeOf b) :
    goal1WitnessStore shapeOf a = goal1WitnessStore shapeOf b := by
  unfold goal1WitnessStore pinnedStore
  rw [hpin, hshape]

private theorem goal1WitnessStore_value_classes
    (shapeOf : Tid → Shape) (classes : List InputValueClass)
    (h : ∀ c ∈ classes, ∀ tid ∈ c.tids,
      isGoal1Packed tid = isGoal1Packed (c.tids.headD 0) ∧
      shapeOf tid = shapeOf (c.tids.headD 0)) :
    InputValueClassesHold classes (goal1WitnessStore shapeOf) := by
  intro c hc tid htid
  exact goal1WitnessStore_eq shapeOf (h c hc tid htid).1 (h c hc tid htid).2

/-- The complete public Goal 1 caller assumptions are jointly satisfiable.
This is stronger than separate witnesses for the value, packed-CU, or label
subcontracts: the same concrete `initSM` and `initPM` also satisfy both shape
environments and every full generated init goal. -/
theorem goal1_external_contract_joint_witness :
    ∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_1InitEnv ∧
      StoreShapesHold initPM pm_goal_1InitEnv ∧
      InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM ∧
      Goal1ExternalInputContract initSM initPM := by
  let initSM := goal1WitnessStore goal1SMShape
  let initPM := goal1WitnessStore goal1PMShape
  refine ⟨initSM, initPM, ?_, ?_, ?_, ?_⟩
  · show StoreShapesHold (goal1WitnessStore goal1SMShape)
      (shapeEnvOfList sm_goal_1InitShapes)
    apply goal1WitnessStore_shapes_hold_of_list
    · intro tid h
      unfold isGoal1Packed at h
      have hp : goal1SMShape tid = [2] ∧ goal1PMShape tid = [2] :=
        of_decide_eq_true h
      exact hp.1
    · native_decide
  · show StoreShapesHold (goal1WitnessStore goal1PMShape)
      (shapeEnvOfList pm_goal_1InitShapes)
    apply goal1WitnessStore_shapes_hold_of_list
    · intro tid h
      unfold isGoal1Packed at h
      have hp : goal1SMShape tid = [2] ∧ goal1PMShape tid = [2] :=
        of_decide_eq_true h
      exact hp.2
    · native_decide
  · show InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals
      (goal1WitnessStore goal1SMShape) (goal1WitnessStore goal1PMShape)
    unfold goal1WitnessStore
    apply pinnedStore2_initGoalsHold
    native_decide
  · unfold Goal1ExternalInputContract
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply goal1WitnessStore_value_classes
      native_decide
    · apply goal1WitnessStore_value_classes
      native_decide
    · show PackedCuSeqlensWF (goal1WitnessStore goal1PMShape 6252) 4096 2
      unfold goal1WitnessStore
      rw [pinnedStore_at_pin 6252 (by native_decide)]
      exact packedCuSeqlens4096_cp2_wf
    · intro l _hl
      show scalarToNat (valAt (goal1WitnessStore goal1PMShape 4931) l) < 154880
      unfold goal1WitnessStore
      rw [pinnedStore_at_nonpin 4931 (by native_decide), valAt_zeroTensor]
      unfold scalarToNat
      norm_num

#print axioms goal1_external_contract_joint_witness

end
end TrainVerify.Denote.GeneratedGoals
