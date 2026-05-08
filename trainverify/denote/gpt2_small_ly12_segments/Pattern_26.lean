/- Auto-generated pattern proof file.
   Pattern: 26
   Hash: 50d559b40c026d8e
   Goals: 31, 33, 81, 82, 106, 131, 133, 181, 182, 232, 258, 281, 282
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_26_goalIds : List Nat := [31, 33, 81, 82, 106, 131, 133, 181, 182, 232, 258, 281, 282]
inductive pattern_26_target : Prop → Prop
  | goal_31 : pattern_26_target goal_31_stmt
  | goal_33 : pattern_26_target goal_33_stmt
  | goal_81 : pattern_26_target goal_81_stmt
  | goal_82 : pattern_26_target goal_82_stmt
  | goal_106 : pattern_26_target goal_106_stmt
  | goal_131 : pattern_26_target goal_131_stmt
  | goal_133 : pattern_26_target goal_133_stmt
  | goal_181 : pattern_26_target goal_181_stmt
  | goal_182 : pattern_26_target goal_182_stmt
  | goal_232 : pattern_26_target goal_232_stmt
  | goal_258 : pattern_26_target goal_258_stmt
  | goal_281 : pattern_26_target goal_281_stmt
  | goal_282 : pattern_26_target goal_282_stmt

def pattern_26_stmt : Prop :=
  ∀ {target : Prop}, pattern_26_target target → target
theorem prove_pattern_26 : pattern_26_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

