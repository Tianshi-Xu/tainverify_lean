/- Auto-generated pattern proof file.
   Pattern: 64
   Hash: 977048be1a457210
   Goals: 145
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_64_goalIds : List Nat := [145]
inductive pattern_64_target : Prop → Prop
  | goal_145 : pattern_64_target goal_145_stmt

def pattern_64_stmt : Prop :=
  ∀ {target : Prop}, pattern_64_target target → target
theorem prove_pattern_64 : pattern_64_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

