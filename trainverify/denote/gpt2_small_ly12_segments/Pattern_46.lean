/- Auto-generated pattern proof file.
   Pattern: 46
   Hash: e00b0161c106a61d
   Goals: 78, 103, 176, 201, 203, 226, 278, 301
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_46_goalIds : List Nat := [78, 103, 176, 201, 203, 226, 278, 301]
inductive pattern_46_target : Prop → Prop
  | goal_78 : pattern_46_target goal_78_stmt
  | goal_103 : pattern_46_target goal_103_stmt
  | goal_176 : pattern_46_target goal_176_stmt
  | goal_201 : pattern_46_target goal_201_stmt
  | goal_203 : pattern_46_target goal_203_stmt
  | goal_226 : pattern_46_target goal_226_stmt
  | goal_278 : pattern_46_target goal_278_stmt
  | goal_301 : pattern_46_target goal_301_stmt

def pattern_46_stmt : Prop :=
  ∀ {target : Prop}, pattern_46_target target → target
theorem prove_pattern_46 : pattern_46_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

