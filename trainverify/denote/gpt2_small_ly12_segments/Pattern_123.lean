/- Auto-generated pattern proof file.
   Pattern: 123
   Hash: 170a42c41124a2b6
   Goals: 359
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_123_goalIds : List Nat := [359]
inductive pattern_123_target : Prop → Prop
  | goal_359 : pattern_123_target goal_359_stmt

def pattern_123_stmt : Prop :=
  ∀ {target : Prop}, pattern_123_target target → target
theorem prove_pattern_123 : pattern_123_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

