/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.PackedCuSeqlensWitness
import denote.yoco_goals.Goal1ExternalContractWitness
import denote.yoco_goals.Goal_2
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.Goal_4
import denote.yoco_goals.Goal_5
import denote.yoco_goals.JointWitnessCore

/-!
# Joint satisfiability of all five public caller contracts

For Goals 2--4, every input whose generated SM and PM shapes are both `[2]`
is pinned to the concrete packed cumulative-sequence tensor `[0, 4096]`; every
other input is a zero tensor of its generated shape.  Goal 5 needs no packed-CU
or value-class premise and uses the corresponding zero stores.  Thus each
existential below uses one concrete store pair for all of that goal's premises.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.JointWitness
open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedGoals
noncomputable section

private def lookupPublicShape (xs : List (Tid × Shape)) (tid : Tid) : Shape :=
  match xs.find? (fun p => p.1 = tid) with
  | some (_, sh) => sh
  | none => []

private def publicPackedPin
    (smShapes pmShapes : List (Tid × Shape)) (tid : Tid) : Bool :=
  decide (lookupPublicShape smShapes tid = [2] ∧
    lookupPublicShape pmShapes tid = [2])

private def publicWitnessStore
    (smShapes pmShapes : List (Tid × Shape)) (sideShapes : List (Tid × Shape)) : Store :=
  pinnedStore (publicPackedPin smShapes pmShapes) (packedCuSeqlensSingle 4096)
    (lookupPublicShape sideShapes)

private theorem publicWitnessStore_shape
    (smShapes pmShapes sideShapes : List (Tid × Shape))
    (hpinShape : ∀ tid, publicPackedPin smShapes pmShapes tid = true →
      lookupPublicShape sideShapes tid = [2]) (tid : Tid) :
    (publicWitnessStore smShapes pmShapes sideShapes tid).shape =
      lookupPublicShape sideShapes tid := by
  unfold publicWitnessStore
  by_cases h : publicPackedPin smShapes pmShapes tid = true
  · rw [pinnedStore_at_pin tid h, packedCuSeqlensSingle_shape, hpinShape tid h]
  · have hf : publicPackedPin smShapes pmShapes tid = false := by
      cases hx : publicPackedPin smShapes pmShapes tid <;> simp_all
    rw [pinnedStore_at_nonpin tid hf]
    rfl

private theorem publicWitnessStore_shapes_hold
    (smShapes pmShapes sideShapes envShapes : List (Tid × Shape))
    (hpinShape : ∀ tid, publicPackedPin smShapes pmShapes tid = true →
      lookupPublicShape sideShapes tid = [2])
    (h : envShapes.all (fun p =>
      decide (lookupPublicShape sideShapes p.1 = p.2)) = true) :
    StoreShapesHold (publicWitnessStore smShapes pmShapes sideShapes)
      (shapeEnvOfList envShapes) := by
  have hz := zeroStore_shapes_hold_of_list
    (shapeOf := lookupPublicShape sideShapes) (xs := envShapes) h
  intro tid sh henv
  rw [publicWitnessStore_shape smShapes pmShapes sideShapes hpinShape]
  have hz' := hz tid sh henv
  rw [zeroStore_shape] at hz'
  exact hz'

private theorem publicWitnessStore_eq
    (smShapes pmShapes sideShapes : List (Tid × Shape)) {a b : Tid}
    (hpin : publicPackedPin smShapes pmShapes a = publicPackedPin smShapes pmShapes b)
    (hshape : lookupPublicShape sideShapes a = lookupPublicShape sideShapes b) :
    publicWitnessStore smShapes pmShapes sideShapes a =
      publicWitnessStore smShapes pmShapes sideShapes b := by
  unfold publicWitnessStore pinnedStore
  rw [hpin, hshape]

private theorem publicWitnessStore_value_classes
    (smShapes pmShapes sideShapes : List (Tid × Shape))
    (classes : List InputValueClass)
    (h : ∀ c ∈ classes, ∀ tid ∈ c.tids,
      publicPackedPin smShapes pmShapes tid =
        publicPackedPin smShapes pmShapes (c.tids.headD 0) ∧
      lookupPublicShape sideShapes tid =
        lookupPublicShape sideShapes (c.tids.headD 0)) :
    InputValueClassesHold classes
      (publicWitnessStore smShapes pmShapes sideShapes) := by
  intro c hc tid htid
  exact publicWitnessStore_eq smShapes pmShapes sideShapes
    (h c hc tid htid).1 (h c hc tid htid).2

private theorem publicWitnessStore_initGoals
    (smShapes pmShapes : List (Tid × Shape)) (numRanks : Nat)
    (goals : List LineageGoal)
    (h : goals.all (pinnedGoalCheck
      (publicPackedPin smShapes pmShapes) (packedCuSeqlensSingle 4096)
      (lookupPublicShape smShapes) (lookupPublicShape pmShapes) numRanks) = true) :
    InitGoalsHold numRanks goals
      (publicWitnessStore smShapes pmShapes smShapes)
      (publicWitnessStore smShapes pmShapes pmShapes) := by
  exact pinnedStore2_initGoalsHold _ _ _ _ _ _ h

private theorem packed_at_public_pin
    (smShapes pmShapes : List (Tid × Shape)) (tid : Tid)
    (h : publicPackedPin smShapes pmShapes tid = true) :
    PackedCuSeqlensWF (publicWitnessStore smShapes pmShapes pmShapes tid) 4096 2 := by
  unfold publicWitnessStore
  rw [pinnedStore_at_pin tid h]
  exact packedCuSeqlens4096_cp2_wf

/-- Every caller premise of the public faithful full Goal 2 contract is
simultaneously inhabited by one concrete pair of stores. -/
theorem goal2_public_contract_joint_witness :
    ∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_2InitEnv ∧
      StoreShapesHold initPM pm_goal_2InitEnv ∧
      InitGoalsHold pm_goal_2.numRanks goal_2_full_initGoals initSM initPM ∧
      Goal2ExternalInputContract initSM initPM := by
  refine ⟨publicWitnessStore smInitShapes pmInitShapes smInitShapes,
    publicWitnessStore smInitShapes pmInitShapes pmInitShapes,
    ?_, ?_, ?_, ?_⟩
  · apply publicWitnessStore_shapes_hold
    · intro tid h
      exact (of_decide_eq_true h).1
    · native_decide
  · apply publicWitnessStore_shapes_hold
    · intro tid h
      exact (of_decide_eq_true h).2
    · native_decide
  · apply publicWitnessStore_initGoals
    native_decide
  · refine ⟨?_, ?_, ?_, ?_⟩
    · apply publicWitnessStore_value_classes
      native_decide
    · apply publicWitnessStore_value_classes
      native_decide
    · exact packed_at_public_pin _ _ 6252 (by native_decide)
    · intro l _hl
      unfold publicWitnessStore
      rw [pinnedStore_at_nonpin 4931 (by native_decide), valAt_zeroTensor]
      unfold scalarToNat
      norm_num

/-- Every caller premise of the public faithful full Goal 3 contract is
simultaneously inhabited by one concrete pair of stores. -/
theorem goal3_public_contract_joint_witness :
    ∃ (initSM initPM : Store),
      StoreShapesHold initSM smInitEnv ∧
      StoreShapesHold initPM pmInitEnv ∧
      InitGoalsHold pm.numRanks initGoals initSM initPM ∧
      Goal3FullExternalInputs initSM initPM := by
  refine ⟨publicWitnessStore smInitShapes pmInitShapes smInitShapes,
    publicWitnessStore smInitShapes pmInitShapes pmInitShapes,
    ?_, ?_, ?_, ?_⟩
  · apply publicWitnessStore_shapes_hold
    · intro tid h
      exact (of_decide_eq_true h).1
    · native_decide
  · apply publicWitnessStore_shapes_hold
    · intro tid h
      exact (of_decide_eq_true h).2
    · native_decide
  · apply publicWitnessStore_initGoals
    native_decide
  · refine ⟨?_, ?_, ?_⟩
    · apply publicWitnessStore_value_classes
      native_decide
    · apply publicWitnessStore_value_classes
      native_decide
    · exact packed_at_public_pin _ _ 6248 (by native_decide)

/-- Every caller premise of the public faithful full Goal 4 contract is
simultaneously inhabited by one concrete pair of stores. -/
theorem goal4_public_contract_joint_witness :
    ∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_4InitEnv ∧
      StoreShapesHold initPM pm_goal_4InitEnv ∧
      InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM ∧
      Goal4ExternalInputContract initSM initPM := by
  refine ⟨publicWitnessStore smInitShapes pmInitShapes smInitShapes,
    publicWitnessStore smInitShapes pmInitShapes pmInitShapes,
    ?_, ?_, ?_, ?_⟩
  · apply publicWitnessStore_shapes_hold
    · intro tid h
      exact (of_decide_eq_true h).1
    · native_decide
  · apply publicWitnessStore_shapes_hold
    · intro tid h
      exact (of_decide_eq_true h).2
    · native_decide
  · apply publicWitnessStore_initGoals
    native_decide
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply publicWitnessStore_value_classes
      native_decide
    · apply publicWitnessStore_value_classes
      native_decide
    all_goals (apply packed_at_public_pin; native_decide)

/-- The public Goal 5 statement has only shape and full-init caller premises;
the same canonical packed/zero stores used above satisfy them jointly. -/
theorem goal5_public_contract_joint_witness :
    ∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_5InitEnv ∧
      StoreShapesHold initPM pm_goal_5InitEnv ∧
      InitGoalsHold pm_goal_5.numRanks goal_5_full_initGoals initSM initPM := by
  refine ⟨publicWitnessStore smInitShapes pmInitShapes smInitShapes,
    publicWitnessStore smInitShapes pmInitShapes pmInitShapes, ?_, ?_, ?_⟩
  · apply publicWitnessStore_shapes_hold
    · intro tid h
      exact (of_decide_eq_true h).1
    · native_decide
  · apply publicWitnessStore_shapes_hold
    · intro tid h
      exact (of_decide_eq_true h).2
    · native_decide
  · apply publicWitnessStore_initGoals
    native_decide

/-- A single exported certificate collecting non-vacuity of every public
`goal_N_stmt_full` caller contract.  Each conjunct supplies an explicit store
pair satisfying all premises of that goal simultaneously. -/
theorem FivePublicContractsJointWitness :
    (∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_1InitEnv ∧
      StoreShapesHold initPM pm_goal_1InitEnv ∧
      InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM ∧
      Goal1ExternalInputContract initSM initPM) ∧
    (∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_2InitEnv ∧
      StoreShapesHold initPM pm_goal_2InitEnv ∧
      InitGoalsHold pm_goal_2.numRanks goal_2_full_initGoals initSM initPM ∧
      Goal2ExternalInputContract initSM initPM) ∧
    (∃ (initSM initPM : Store),
      StoreShapesHold initSM smInitEnv ∧
      StoreShapesHold initPM pmInitEnv ∧
      InitGoalsHold pm.numRanks initGoals initSM initPM ∧
      Goal3FullExternalInputs initSM initPM) ∧
    (∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_4InitEnv ∧
      StoreShapesHold initPM pm_goal_4InitEnv ∧
      InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM ∧
      Goal4ExternalInputContract initSM initPM) ∧
    (∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_5InitEnv ∧
      StoreShapesHold initPM pm_goal_5InitEnv ∧
      InitGoalsHold pm_goal_5.numRanks goal_5_full_initGoals initSM initPM) := by
  exact ⟨goal1_external_contract_joint_witness,
    goal2_public_contract_joint_witness,
    goal3_public_contract_joint_witness,
    goal4_public_contract_joint_witness,
    goal5_public_contract_joint_witness⟩

#print axioms goal2_public_contract_joint_witness
#print axioms goal3_public_contract_joint_witness
#print axioms goal4_public_contract_joint_witness
#print axioms goal5_public_contract_joint_witness
#print axioms FivePublicContractsJointWitness

end
end TrainVerify.Denote.GeneratedGoals
