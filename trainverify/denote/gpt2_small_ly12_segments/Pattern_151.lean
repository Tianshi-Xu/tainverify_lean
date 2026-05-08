/- Auto-generated pattern proof file.
   Pattern: 151
   Hash: a7461b0038e341b6
   Goals: 415, 450, 546, 730
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_151_goalIds : List Nat := [415, 450, 546, 730]
inductive pattern_151_target : Prop → Prop
  | goal_415 : pattern_151_target goal_415_stmt
  | goal_450 : pattern_151_target goal_450_stmt
  | goal_546 : pattern_151_target goal_546_stmt
  | goal_730 : pattern_151_target goal_730_stmt

def pattern_151_stmt : Prop :=
  ∀ {target : Prop}, pattern_151_target target → target
theorem prove_pattern_151 : pattern_151_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

