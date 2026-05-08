/- Auto-generated pattern proof file.
   Pattern: 127
   Hash: d2e2a2bd15b78ef5
   Goals: 364, 399, 469, 504, 539, 609, 714
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_127_goalIds : List Nat := [364, 399, 469, 504, 539, 609, 714]
inductive pattern_127_target : Prop → Prop
  | goal_364 : pattern_127_target goal_364_stmt
  | goal_399 : pattern_127_target goal_399_stmt
  | goal_469 : pattern_127_target goal_469_stmt
  | goal_504 : pattern_127_target goal_504_stmt
  | goal_539 : pattern_127_target goal_539_stmt
  | goal_609 : pattern_127_target goal_609_stmt
  | goal_714 : pattern_127_target goal_714_stmt

def pattern_127_stmt : Prop :=
  ∀ {target : Prop}, pattern_127_target target → target
theorem prove_pattern_127 : pattern_127_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

