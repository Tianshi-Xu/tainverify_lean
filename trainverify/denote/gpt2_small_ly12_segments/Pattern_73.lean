/- Auto-generated pattern proof file.
   Pattern: 73
   Hash: 4d771498e0018a7e
   Goals: 192
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_73_goalIds : List Nat := [192]
inductive pattern_73_target : Prop → Prop
  | goal_192 : pattern_73_target goal_192_stmt

def pattern_73_stmt : Prop :=
  ∀ {target : Prop}, pattern_73_target target → target
theorem prove_pattern_73 : pattern_73_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

