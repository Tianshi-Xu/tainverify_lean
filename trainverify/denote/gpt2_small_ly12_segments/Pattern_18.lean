/- Auto-generated pattern proof file.
   Pattern: 18
   Hash: cbe3e5f51755a532
   Goals: 21, 196
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_18_goalIds : List Nat := [21, 196]
inductive pattern_18_target : Prop → Prop
  | goal_21 : pattern_18_target goal_21_stmt
  | goal_196 : pattern_18_target goal_196_stmt

def pattern_18_stmt : Prop :=
  ∀ {target : Prop}, pattern_18_target target → target
theorem prove_pattern_18 : pattern_18_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

