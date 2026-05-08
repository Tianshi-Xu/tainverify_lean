/- Auto-generated pattern proof file.
   Pattern: 133
   Hash: 351a6e0e58da6703
   Goals: 377
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_133_goalIds : List Nat := [377]
inductive pattern_133_target : Prop → Prop
  | goal_377 : pattern_133_target goal_377_stmt

def pattern_133_stmt : Prop :=
  ∀ {target : Prop}, pattern_133_target target → target
theorem prove_pattern_133 : pattern_133_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

