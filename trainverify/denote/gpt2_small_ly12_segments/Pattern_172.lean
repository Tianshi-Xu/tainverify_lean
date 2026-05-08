/- Auto-generated pattern proof file.
   Pattern: 172
   Hash: ada7ceddaf72074d
   Goals: 503, 538
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_172_goalIds : List Nat := [503, 538]
inductive pattern_172_target : Prop → Prop
  | goal_503 : pattern_172_target goal_503_stmt
  | goal_538 : pattern_172_target goal_538_stmt

def pattern_172_stmt : Prop :=
  ∀ {target : Prop}, pattern_172_target target → target
theorem prove_pattern_172 : pattern_172_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

