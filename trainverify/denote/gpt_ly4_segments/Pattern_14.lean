/- Auto-generated pattern proof file.
   Pattern: 14
   Hash: 453513444068c2dd
   Goals: 18
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_14_goalIds : List Nat := [18]
inductive pattern_14_target : Prop → Prop
  | goal_18 : pattern_14_target goal_18_stmt

def pattern_14_stmt : Prop :=
  ∀ {target : Prop}, pattern_14_target target → target
theorem prove_pattern_14 : pattern_14_stmt := by
  intro target h
  cases h with
  | goal_18 =>
      sorry

end TrainVerify.Denote.GeneratedPatterns

