/- Auto-generated pattern proof file.
   Pattern: 80
   Hash: d139844ec7778cd9
   Goals: 143
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_80_goalIds : List Nat := [143]
inductive pattern_80_target : Prop → Prop
  | goal_143 : pattern_80_target goal_143_stmt

def pattern_80_stmt : Prop :=
  ∀ {target : Prop}, pattern_80_target target → target
theorem prove_pattern_80 : pattern_80_stmt := by
  intro target h
  cases h with
  | goal_143 =>
      sorry

end TrainVerify.Denote.GeneratedPatterns

