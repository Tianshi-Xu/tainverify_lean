/- Auto-generated pattern proof file.
   Pattern: 77
   Hash: 7c52e5bc0cd0d2e6
   Goals: 202, 227
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_77_goalIds : List Nat := [202, 227]
inductive pattern_77_target : Prop → Prop
  | goal_202 : pattern_77_target goal_202_stmt
  | goal_227 : pattern_77_target goal_227_stmt

def pattern_77_stmt : Prop :=
  ∀ {target : Prop}, pattern_77_target target → target
theorem prove_pattern_77 : pattern_77_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

