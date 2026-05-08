/- Auto-generated pattern proof file.
   Pattern: 221
   Hash: 937a885642ea4bfc
   Goals: 771, 799, 827, 855, 883
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_221_goalIds : List Nat := [771, 799, 827, 855, 883]
inductive pattern_221_target : Prop → Prop
  | goal_771 : pattern_221_target goal_771_stmt
  | goal_799 : pattern_221_target goal_799_stmt
  | goal_827 : pattern_221_target goal_827_stmt
  | goal_855 : pattern_221_target goal_855_stmt
  | goal_883 : pattern_221_target goal_883_stmt

def pattern_221_stmt : Prop :=
  ∀ {target : Prop}, pattern_221_target target → target
theorem prove_pattern_221 : pattern_221_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

