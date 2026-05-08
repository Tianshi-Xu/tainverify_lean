/- Auto-generated pattern proof file.
   Pattern: 197
   Hash: c6ceff1d1b76603d
   Goals: 676
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_197_goalIds : List Nat := [676]
inductive pattern_197_target : Prop → Prop
  | goal_676 : pattern_197_target goal_676_stmt

def pattern_197_stmt : Prop :=
  ∀ {target : Prop}, pattern_197_target target → target
theorem prove_pattern_197 : pattern_197_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

