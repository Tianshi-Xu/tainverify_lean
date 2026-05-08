/- Auto-generated pattern proof file.
   Pattern: 121
   Hash: bb170cc2ef1a2985
   Goals: 356, 395, 430, 463, 465, 496, 498, 500, 566, 603, 605, 638, 708
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_121_goalIds : List Nat := [356, 395, 430, 463, 465, 496, 498, 500, 566, 603, 605, 638, 708]
inductive pattern_121_target : Prop → Prop
  | goal_356 : pattern_121_target goal_356_stmt
  | goal_395 : pattern_121_target goal_395_stmt
  | goal_430 : pattern_121_target goal_430_stmt
  | goal_463 : pattern_121_target goal_463_stmt
  | goal_465 : pattern_121_target goal_465_stmt
  | goal_496 : pattern_121_target goal_496_stmt
  | goal_498 : pattern_121_target goal_498_stmt
  | goal_500 : pattern_121_target goal_500_stmt
  | goal_566 : pattern_121_target goal_566_stmt
  | goal_603 : pattern_121_target goal_603_stmt
  | goal_605 : pattern_121_target goal_605_stmt
  | goal_638 : pattern_121_target goal_638_stmt
  | goal_708 : pattern_121_target goal_708_stmt

def pattern_121_stmt : Prop :=
  ∀ {target : Prop}, pattern_121_target target → target
theorem prove_pattern_121 : pattern_121_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

