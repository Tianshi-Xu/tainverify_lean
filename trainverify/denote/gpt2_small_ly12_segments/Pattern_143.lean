/- Auto-generated pattern proof file.
   Pattern: 143
   Hash: 703e5d721b446e93
   Goals: 398, 643
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_143_goalIds : List Nat := [398, 643]
inductive pattern_143_target : Prop → Prop
  | goal_398 : pattern_143_target goal_398_stmt
  | goal_643 : pattern_143_target goal_643_stmt

def pattern_143_stmt : Prop :=
  ∀ {target : Prop}, pattern_143_target target → target
theorem prove_pattern_143 : pattern_143_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

