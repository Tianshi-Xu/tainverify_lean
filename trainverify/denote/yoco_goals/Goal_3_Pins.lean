/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.Pattern_3

/-!
# Discharge Goal 3's twelve cu-seqlens pins from generated provenance

The twelve cut-boundary tids are not arbitrary independent inputs: the generator
records all of them in the same immutable `cu_seqlens_k` input value class.
Consequently one anchor value plus `InputValueClassesHold` implies every pin.
-/

set_option linter.style.longLine false
set_option maxRecDepth 1000000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.GeneratedPatterns

namespace TrainVerify.Denote.YocoMoE.Goal3Pins

private def cuKClass : InputValueClass :=
  { source := "getitem:root=4188:key=cu_seqlens_k",
    tids := [4695, 4749, 4803, 4857, 4911, 4965, 5019, 5073, 5127, 5181,
      5235, 5289, 5346, 5395, 5444, 5493, 5542, 5591, 5640, 5689, 5738,
      5787, 5836, 5885] }

private theorem cuKClass_mem : cuKClass ∈ pmInputValueClasses := by native_decide

private theorem cu_k_pin_of_value_class (initPM : Store)
    (hValues : InputValueClassesHold pmInputValueClasses initPM)
    (hAnchor : initPM 4695 = cu_pin_value)
    (tid : Tid) (htid : tid ∈ cuKClass.tids) :
    initPM tid = cu_pin_value := by
  have heq : initPM tid = initPM 4695 :=
    hValues.eq_of_mem cuKClass_mem htid (by native_decide)
  exact heq.trans hAnchor

/-- The provenance-plus-anchor contract is jointly satisfiable: a single
constant store witnesses every generated value class and the anchor equation. -/
theorem value_class_anchor_witness :
    ∃ initPM : Store,
      InputValueClassesHold pmInputValueClasses initPM ∧
      initPM 4695 = cu_pin_value := by
  refine ⟨fun _ => cu_pin_value, ?_, rfl⟩
  exact inputValueClassesHold_const pmInputValueClasses cu_pin_value

/-- Goal 3 with its twelve explicit pins discharged from the generated
same-source input contract and one concrete anchor value. -/
def goal_3_stmt_with_value_class : Prop :=
  ∀ (initSM initPM : Store),
    StoreShapesHold initSM sm_goal_3InitEnv →
    StoreShapesHold initPM pm_goal_3InitEnv →
    InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM →
    InputValueClassesHold pmInputValueClasses initPM →
    initPM 4695 = cu_pin_value →
    let smStore := denoteGraph_ringAttn sm_goal_3 initSM
    let pmStore := denoteGraph_ringAttn pm_goal_3 initPM
    let ts := smStore goal_3_cut_goal.ts
    let tps := goal_3_cut_goal.tps.map (fun p => pmStore p.tid)
    ts.shape = goal_3_cut_goal.tsShape ∧
      (tps.map (fun t => t.shape)) = goal_3_cut_goal.tpShapes ∧
      ts = reconstructWithDim goal_3_cut_goal.gatherDim pm_goal_3.numRanks 0 tps

/-- The twelve pins are now derived, not caller-supplied independently. -/
theorem prove_goal_3_from_value_class : goal_3_stmt_with_value_class := by
  intro initSM initPM hSM hPM hInit hValues hAnchor
  apply prove_goal_3 initSM initPM hSM hPM hInit
  all_goals
    apply cu_k_pin_of_value_class initPM hValues hAnchor
    native_decide

end TrainVerify.Denote.YocoMoE.Goal3Pins
