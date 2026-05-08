/- Auto-generated pattern proof file.
   Pattern: 147
   Hash: 5693f5d6954802d2
   Goals: 404, 439, 509, 614, 649
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_147_goalIds : List Nat := [404, 439, 509, 614, 649]
inductive pattern_147_target : Prop → Prop
  | goal_404 : pattern_147_target goal_404_stmt
  | goal_439 : pattern_147_target goal_439_stmt
  | goal_509 : pattern_147_target goal_509_stmt
  | goal_614 : pattern_147_target goal_614_stmt
  | goal_649 : pattern_147_target goal_649_stmt

def pattern_147_stmt : Prop :=
  ∀ {target : Prop}, pattern_147_target target → target
theorem prove_pattern_147 : pattern_147_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

