/- Auto-generated pattern proof file.
   Pattern: 90
   Hash: d36f1761f4e16e1d
   Goals: 309
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_90_goalIds : List Nat := [309]
inductive pattern_90_target : Prop → Prop
  | goal_309 : pattern_90_target goal_309_stmt

def pattern_90_stmt : Prop :=
  ∀ {target : Prop}, pattern_90_target target → target
theorem prove_pattern_90 : pattern_90_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

