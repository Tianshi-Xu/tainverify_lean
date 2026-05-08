/- Auto-generated pattern proof file.
   Pattern: 189
   Hash: c3c1c8e49fe03d78
   Goals: 587, 622
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_189_goalIds : List Nat := [587, 622]
inductive pattern_189_target : Prop → Prop
  | goal_587 : pattern_189_target goal_587_stmt
  | goal_622 : pattern_189_target goal_622_stmt

def pattern_189_stmt : Prop :=
  ∀ {target : Prop}, pattern_189_target target → target
theorem prove_pattern_189 : pattern_189_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

