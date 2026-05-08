/- Auto-generated pattern proof file.
   Pattern: 129
   Hash: 38db11f8b0e656b3
   Goals: 366
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_129_goalIds : List Nat := [366]
inductive pattern_129_target : Prop → Prop
  | goal_366 : pattern_129_target goal_366_stmt

def pattern_129_stmt : Prop :=
  ∀ {target : Prop}, pattern_129_target target → target
theorem prove_pattern_129 : pattern_129_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

