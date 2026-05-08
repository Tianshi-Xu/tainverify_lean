/- Auto-generated pattern proof file.
   Pattern: 219
   Hash: e225aa80702b3daa
   Goals: 765, 775, 779, 789, 793, 807, 821, 831, 859, 873
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_219_goalIds : List Nat := [765, 775, 779, 789, 793, 807, 821, 831, 859, 873]
inductive pattern_219_target : Prop → Prop
  | goal_765 : pattern_219_target goal_765_stmt
  | goal_775 : pattern_219_target goal_775_stmt
  | goal_779 : pattern_219_target goal_779_stmt
  | goal_789 : pattern_219_target goal_789_stmt
  | goal_793 : pattern_219_target goal_793_stmt
  | goal_807 : pattern_219_target goal_807_stmt
  | goal_821 : pattern_219_target goal_821_stmt
  | goal_831 : pattern_219_target goal_831_stmt
  | goal_859 : pattern_219_target goal_859_stmt
  | goal_873 : pattern_219_target goal_873_stmt

def pattern_219_stmt : Prop :=
  ∀ {target : Prop}, pattern_219_target target → target
theorem prove_pattern_219 : pattern_219_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

