/- Auto-generated pattern proof file.
   Pattern: 132
   Hash: 157c7a9d3db61347
   Goals: 372, 477, 512, 591, 626, 722
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_132_goalIds : List Nat := [372, 477, 512, 591, 626, 722]
inductive pattern_132_target : Prop → Prop
  | goal_372 : pattern_132_target goal_372_stmt
  | goal_477 : pattern_132_target goal_477_stmt
  | goal_512 : pattern_132_target goal_512_stmt
  | goal_591 : pattern_132_target goal_591_stmt
  | goal_626 : pattern_132_target goal_626_stmt
  | goal_722 : pattern_132_target goal_722_stmt

def pattern_132_stmt : Prop :=
  ∀ {target : Prop}, pattern_132_target target → target
theorem prove_pattern_132 : pattern_132_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

