/- Auto-generated pattern proof file.
   Pattern: 8
   Hash: e82f3b2e5c42daaa
   Goals: 9, 11, 13, 34, 36, 38, 59, 61, 63, 84, 86, 88
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_8_goalIds : List Nat := [9, 11, 13, 34, 36, 38, 59, 61, 63, 84, 86, 88]
inductive pattern_8_target : Prop → Prop
  | goal_9 : pattern_8_target goal_9_stmt
  | goal_11 : pattern_8_target goal_11_stmt
  | goal_13 : pattern_8_target goal_13_stmt
  | goal_34 : pattern_8_target goal_34_stmt
  | goal_36 : pattern_8_target goal_36_stmt
  | goal_38 : pattern_8_target goal_38_stmt
  | goal_59 : pattern_8_target goal_59_stmt
  | goal_61 : pattern_8_target goal_61_stmt
  | goal_63 : pattern_8_target goal_63_stmt
  | goal_84 : pattern_8_target goal_84_stmt
  | goal_86 : pattern_8_target goal_86_stmt
  | goal_88 : pattern_8_target goal_88_stmt

def pattern_8_stmt : Prop :=
  ∀ {target : Prop}, pattern_8_target target → target
theorem prove_pattern_8 : pattern_8_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

