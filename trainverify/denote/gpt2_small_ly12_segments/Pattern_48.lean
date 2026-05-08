/- Auto-generated pattern proof file.
   Pattern: 48
   Hash: feaf0a8f2f7db76b
   Goals: 90
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_48_goalIds : List Nat := [90]
inductive pattern_48_target : Prop → Prop
  | goal_90 : pattern_48_target goal_90_stmt

def pattern_48_stmt : Prop :=
  ∀ {target : Prop}, pattern_48_target target → target
theorem prove_pattern_48 : pattern_48_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

