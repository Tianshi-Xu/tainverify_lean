/- Auto-generated pattern proof file.
   Pattern: 115
   Hash: 9ccba3af8a3158d9
   Goals: 341, 344, 370, 376, 475, 484, 580, 656
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_115_goalIds : List Nat := [341, 344, 370, 376, 475, 484, 580, 656]
inductive pattern_115_target : Prop → Prop
  | goal_341 : pattern_115_target goal_341_stmt
  | goal_344 : pattern_115_target goal_344_stmt
  | goal_370 : pattern_115_target goal_370_stmt
  | goal_376 : pattern_115_target goal_376_stmt
  | goal_475 : pattern_115_target goal_475_stmt
  | goal_484 : pattern_115_target goal_484_stmt
  | goal_580 : pattern_115_target goal_580_stmt
  | goal_656 : pattern_115_target goal_656_stmt

def pattern_115_stmt : Prop :=
  ∀ {target : Prop}, pattern_115_target target → target
theorem prove_pattern_115 : pattern_115_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

