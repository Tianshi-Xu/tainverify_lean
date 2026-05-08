/- Auto-generated pattern proof file.
   Pattern: 12
   Hash: c7dd4a63a6fafe17
   Goals: 15, 165
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_12_goalIds : List Nat := [15, 165]
inductive pattern_12_target : Prop → Prop
  | goal_15 : pattern_12_target goal_15_stmt
  | goal_165 : pattern_12_target goal_165_stmt

def pattern_12_stmt : Prop :=
  ∀ {target : Prop}, pattern_12_target target → target
theorem prove_pattern_12 : pattern_12_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

