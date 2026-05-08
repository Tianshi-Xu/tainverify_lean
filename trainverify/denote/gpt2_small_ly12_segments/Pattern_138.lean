/- Auto-generated pattern proof file.
   Pattern: 138
   Hash: 250cf696de15b580
   Goals: 384, 594
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_138_goalIds : List Nat := [384, 594]
inductive pattern_138_target : Prop → Prop
  | goal_384 : pattern_138_target goal_384_stmt
  | goal_594 : pattern_138_target goal_594_stmt

def pattern_138_stmt : Prop :=
  ∀ {target : Prop}, pattern_138_target target → target
theorem prove_pattern_138 : pattern_138_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

