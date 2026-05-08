/- Auto-generated pattern proof file.
   Pattern: 148
   Hash: 566a03d6acd2c3a2
   Goals: 405, 440, 510, 615, 650
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_148_goalIds : List Nat := [405, 440, 510, 615, 650]
inductive pattern_148_target : Prop → Prop
  | goal_405 : pattern_148_target goal_405_stmt
  | goal_440 : pattern_148_target goal_440_stmt
  | goal_510 : pattern_148_target goal_510_stmt
  | goal_615 : pattern_148_target goal_615_stmt
  | goal_650 : pattern_148_target goal_650_stmt

def pattern_148_stmt : Prop :=
  ∀ {target : Prop}, pattern_148_target target → target
theorem prove_pattern_148 : pattern_148_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

