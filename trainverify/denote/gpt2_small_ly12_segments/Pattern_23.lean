/- Auto-generated pattern proof file.
   Pattern: 23
   Hash: 079c368d91506bb2
   Goals: 26, 28, 48, 51, 123, 128, 198, 251
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_23_goalIds : List Nat := [26, 28, 48, 51, 123, 128, 198, 251]
inductive pattern_23_target : Prop → Prop
  | goal_26 : pattern_23_target goal_26_stmt
  | goal_28 : pattern_23_target goal_28_stmt
  | goal_48 : pattern_23_target goal_48_stmt
  | goal_51 : pattern_23_target goal_51_stmt
  | goal_123 : pattern_23_target goal_123_stmt
  | goal_128 : pattern_23_target goal_128_stmt
  | goal_198 : pattern_23_target goal_198_stmt
  | goal_251 : pattern_23_target goal_251_stmt

def pattern_23_stmt : Prop :=
  ∀ {target : Prop}, pattern_23_target target → target
theorem prove_pattern_23 : pattern_23_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

