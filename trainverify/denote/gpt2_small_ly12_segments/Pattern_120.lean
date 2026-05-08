/- Auto-generated pattern proof file.
   Pattern: 120
   Hash: 311c9abadc02f73b
   Goals: 350, 354, 420, 422, 455, 490, 494, 560, 562, 632, 669, 700, 702
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_120_goalIds : List Nat := [350, 354, 420, 422, 455, 490, 494, 560, 562, 632, 669, 700, 702]
inductive pattern_120_target : Prop → Prop
  | goal_350 : pattern_120_target goal_350_stmt
  | goal_354 : pattern_120_target goal_354_stmt
  | goal_420 : pattern_120_target goal_420_stmt
  | goal_422 : pattern_120_target goal_422_stmt
  | goal_455 : pattern_120_target goal_455_stmt
  | goal_490 : pattern_120_target goal_490_stmt
  | goal_494 : pattern_120_target goal_494_stmt
  | goal_560 : pattern_120_target goal_560_stmt
  | goal_562 : pattern_120_target goal_562_stmt
  | goal_632 : pattern_120_target goal_632_stmt
  | goal_669 : pattern_120_target goal_669_stmt
  | goal_700 : pattern_120_target goal_700_stmt
  | goal_702 : pattern_120_target goal_702_stmt

def pattern_120_stmt : Prop :=
  ∀ {target : Prop}, pattern_120_target target → target
theorem prove_pattern_120 : pattern_120_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

