/- Auto-generated pattern proof file.
   Pattern: 17
   Hash: cbe3e5f51755a532
   Goals: 21
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_17_goalIds : List Nat := [21]
inductive pattern_17_target : Prop → Prop
  | goal_21 : pattern_17_target goal_21_stmt

def pattern_17_stmt : Prop :=
  ∀ {target : Prop}, pattern_17_target target → target
theorem prove_pattern_17 : pattern_17_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

