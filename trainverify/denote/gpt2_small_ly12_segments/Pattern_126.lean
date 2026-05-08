/- Auto-generated pattern proof file.
   Pattern: 126
   Hash: f2e0c380f006cf32
   Goals: 363, 433, 468, 608
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_126_goalIds : List Nat := [363, 433, 468, 608]
inductive pattern_126_target : Prop → Prop
  | goal_363 : pattern_126_target goal_363_stmt
  | goal_433 : pattern_126_target goal_433_stmt
  | goal_468 : pattern_126_target goal_468_stmt
  | goal_608 : pattern_126_target goal_608_stmt

def pattern_126_stmt : Prop :=
  ∀ {target : Prop}, pattern_126_target target → target
theorem prove_pattern_126 : pattern_126_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

