/- Auto-generated pattern proof file.
   Pattern: 13
   Hash: 7b2190bf8a3838fe
   Goals: 16, 94, 119, 141, 166, 219, 241, 266
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_13_goalIds : List Nat := [16, 94, 119, 141, 166, 219, 241, 266]
inductive pattern_13_target : Prop → Prop
  | goal_16 : pattern_13_target goal_16_stmt
  | goal_94 : pattern_13_target goal_94_stmt
  | goal_119 : pattern_13_target goal_119_stmt
  | goal_141 : pattern_13_target goal_141_stmt
  | goal_166 : pattern_13_target goal_166_stmt
  | goal_219 : pattern_13_target goal_219_stmt
  | goal_241 : pattern_13_target goal_241_stmt
  | goal_266 : pattern_13_target goal_266_stmt

def pattern_13_stmt : Prop :=
  ∀ {target : Prop}, pattern_13_target target → target
theorem prove_pattern_13 : pattern_13_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

