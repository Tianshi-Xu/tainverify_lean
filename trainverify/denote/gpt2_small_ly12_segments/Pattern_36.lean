/- Auto-generated pattern proof file.
   Pattern: 36
   Hash: 408903fe855a8e8a
   Goals: 53, 76, 101, 126, 151, 228, 276, 306
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_36_goalIds : List Nat := [53, 76, 101, 126, 151, 228, 276, 306]
inductive pattern_36_target : Prop → Prop
  | goal_53 : pattern_36_target goal_53_stmt
  | goal_76 : pattern_36_target goal_76_stmt
  | goal_101 : pattern_36_target goal_101_stmt
  | goal_126 : pattern_36_target goal_126_stmt
  | goal_151 : pattern_36_target goal_151_stmt
  | goal_228 : pattern_36_target goal_228_stmt
  | goal_276 : pattern_36_target goal_276_stmt
  | goal_306 : pattern_36_target goal_306_stmt

def pattern_36_stmt : Prop :=
  ∀ {target : Prop}, pattern_36_target target → target
theorem prove_pattern_36 : pattern_36_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

