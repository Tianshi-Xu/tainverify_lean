/- Auto-generated pattern proof file.
   Pattern: 11
   Hash: e28141bffb9a2f8d
   Goals: 14, 39, 62, 87, 110, 187, 210, 262, 264, 285
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_11_goalIds : List Nat := [14, 39, 62, 87, 110, 187, 210, 262, 264, 285]
inductive pattern_11_target : Prop → Prop
  | goal_14 : pattern_11_target goal_14_stmt
  | goal_39 : pattern_11_target goal_39_stmt
  | goal_62 : pattern_11_target goal_62_stmt
  | goal_87 : pattern_11_target goal_87_stmt
  | goal_110 : pattern_11_target goal_110_stmt
  | goal_187 : pattern_11_target goal_187_stmt
  | goal_210 : pattern_11_target goal_210_stmt
  | goal_262 : pattern_11_target goal_262_stmt
  | goal_264 : pattern_11_target goal_264_stmt
  | goal_285 : pattern_11_target goal_285_stmt

def pattern_11_stmt : Prop :=
  ∀ {target : Prop}, pattern_11_target target → target
theorem prove_pattern_11 : pattern_11_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

