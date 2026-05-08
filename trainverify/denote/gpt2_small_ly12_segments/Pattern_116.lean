/- Auto-generated pattern proof file.
   Pattern: 116
   Hash: 6522a801ae6873b5
   Goals: 342, 412, 447, 657, 692
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_116_goalIds : List Nat := [342, 412, 447, 657, 692]
inductive pattern_116_target : Prop → Prop
  | goal_342 : pattern_116_target goal_342_stmt
  | goal_412 : pattern_116_target goal_412_stmt
  | goal_447 : pattern_116_target goal_447_stmt
  | goal_657 : pattern_116_target goal_657_stmt
  | goal_692 : pattern_116_target goal_692_stmt

def pattern_116_stmt : Prop :=
  ∀ {target : Prop}, pattern_116_target target → target
theorem prove_pattern_116 : pattern_116_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

