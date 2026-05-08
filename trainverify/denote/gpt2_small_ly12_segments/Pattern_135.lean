/- Auto-generated pattern proof file.
   Pattern: 135
   Hash: b942d6dc327ef4b3
   Goals: 379, 411, 446, 481, 516, 624, 691, 735
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_135_goalIds : List Nat := [379, 411, 446, 481, 516, 624, 691, 735]
inductive pattern_135_target : Prop → Prop
  | goal_379 : pattern_135_target goal_379_stmt
  | goal_411 : pattern_135_target goal_411_stmt
  | goal_446 : pattern_135_target goal_446_stmt
  | goal_481 : pattern_135_target goal_481_stmt
  | goal_516 : pattern_135_target goal_516_stmt
  | goal_624 : pattern_135_target goal_624_stmt
  | goal_691 : pattern_135_target goal_691_stmt
  | goal_735 : pattern_135_target goal_735_stmt

def pattern_135_stmt : Prop :=
  ∀ {target : Prop}, pattern_135_target target → target
theorem prove_pattern_135 : pattern_135_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

