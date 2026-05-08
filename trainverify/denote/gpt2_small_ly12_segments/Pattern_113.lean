/- Auto-generated pattern proof file.
   Pattern: 113
   Hash: 810a701986593b44
   Goals: 336, 590, 660, 686, 695, 721
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_113_goalIds : List Nat := [336, 590, 660, 686, 695, 721]
inductive pattern_113_target : Prop → Prop
  | goal_336 : pattern_113_target goal_336_stmt
  | goal_590 : pattern_113_target goal_590_stmt
  | goal_660 : pattern_113_target goal_660_stmt
  | goal_686 : pattern_113_target goal_686_stmt
  | goal_695 : pattern_113_target goal_695_stmt
  | goal_721 : pattern_113_target goal_721_stmt

def pattern_113_stmt : Prop :=
  ∀ {target : Prop}, pattern_113_target target → target
theorem prove_pattern_113 : pattern_113_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

