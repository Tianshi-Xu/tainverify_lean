/- Auto-generated pattern proof file.
   Pattern: 213
   Hash: aed5adffc490ef93
   Goals: 745, 801, 829
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_213_goalIds : List Nat := [745, 801, 829]
inductive pattern_213_target : Prop → Prop
  | goal_745 : pattern_213_target goal_745_stmt
  | goal_801 : pattern_213_target goal_801_stmt
  | goal_829 : pattern_213_target goal_829_stmt

def pattern_213_stmt : Prop :=
  ∀ {target : Prop}, pattern_213_target target → target
theorem prove_pattern_213 : pattern_213_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

