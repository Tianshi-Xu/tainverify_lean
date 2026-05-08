/- Auto-generated pattern proof file.
   Pattern: 150
   Hash: 1b4403d68cc65102
   Goals: 414, 449, 551, 586, 589, 621, 694, 726
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_150_goalIds : List Nat := [414, 449, 551, 586, 589, 621, 694, 726]
inductive pattern_150_target : Prop → Prop
  | goal_414 : pattern_150_target goal_414_stmt
  | goal_449 : pattern_150_target goal_449_stmt
  | goal_551 : pattern_150_target goal_551_stmt
  | goal_586 : pattern_150_target goal_586_stmt
  | goal_589 : pattern_150_target goal_589_stmt
  | goal_621 : pattern_150_target goal_621_stmt
  | goal_694 : pattern_150_target goal_694_stmt
  | goal_726 : pattern_150_target goal_726_stmt

def pattern_150_stmt : Prop :=
  ∀ {target : Prop}, pattern_150_target target → target
theorem prove_pattern_150 : pattern_150_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

