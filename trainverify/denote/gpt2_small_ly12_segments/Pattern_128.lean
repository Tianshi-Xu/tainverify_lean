/- Auto-generated pattern proof file.
   Pattern: 128
   Hash: 16c7c037822ff585
   Goals: 365
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_128_goalIds : List Nat := [365]
inductive pattern_128_target : Prop → Prop
  | goal_365 : pattern_128_target goal_365_stmt

def pattern_128_stmt : Prop :=
  ∀ {target : Prop}, pattern_128_target target → target
theorem prove_pattern_128 : pattern_128_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

