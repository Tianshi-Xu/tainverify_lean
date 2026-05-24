/- Auto-generated pattern proof file.
   Pattern: 115
   Hash: c3c1c8e49fe03d78
   Goals: 212, 247
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_115_goalIds : List Nat := [212, 247]
inductive pattern_115_target : Prop → Prop
  | goal_212 : pattern_115_target goal_212_stmt
  | goal_247 : pattern_115_target goal_247_stmt

def pattern_115_stmt : Prop :=
  ∀ {target : Prop}, pattern_115_target target → target
theorem prove_pattern_115 : pattern_115_stmt := by
  intro target h
  cases h with
  | goal_212 =>
      sorry
  | goal_247 =>
      sorry

end TrainVerify.Denote.GeneratedPatterns

