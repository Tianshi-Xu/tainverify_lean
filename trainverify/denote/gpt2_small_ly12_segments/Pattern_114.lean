/- Auto-generated pattern proof file.
   Pattern: 114
   Hash: 2c9154fd373a643c
   Goals: 340, 375, 655
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_114_goalIds : List Nat := [340, 375, 655]
inductive pattern_114_target : Prop → Prop
  | goal_340 : pattern_114_target goal_340_stmt
  | goal_375 : pattern_114_target goal_375_stmt
  | goal_655 : pattern_114_target goal_655_stmt

def pattern_114_stmt : Prop :=
  ∀ {target : Prop}, pattern_114_target target → target
theorem prove_pattern_114 : pattern_114_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

