/- Auto-generated pattern proof file.
   Pattern: 223
   Hash: 00bacb9874e28a00
   Goals: 778, 792, 824, 904
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_223_goalIds : List Nat := [778, 792, 824, 904]
inductive pattern_223_target : Prop → Prop
  | goal_778 : pattern_223_target goal_778_stmt
  | goal_792 : pattern_223_target goal_792_stmt
  | goal_824 : pattern_223_target goal_824_stmt
  | goal_904 : pattern_223_target goal_904_stmt

def pattern_223_stmt : Prop :=
  ∀ {target : Prop}, pattern_223_target target → target
theorem prove_pattern_223 : pattern_223_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

