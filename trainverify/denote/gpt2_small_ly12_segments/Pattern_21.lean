/- Auto-generated pattern proof file.
   Pattern: 21
   Hash: c118a3d5c38253d9
   Goals: 24, 204, 254, 274, 279, 299
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_21_goalIds : List Nat := [24, 204, 254, 274, 279, 299]
inductive pattern_21_target : Prop → Prop
  | goal_24 : pattern_21_target goal_24_stmt
  | goal_204 : pattern_21_target goal_204_stmt
  | goal_254 : pattern_21_target goal_254_stmt
  | goal_274 : pattern_21_target goal_274_stmt
  | goal_279 : pattern_21_target goal_279_stmt
  | goal_299 : pattern_21_target goal_299_stmt

def pattern_21_stmt : Prop :=
  ∀ {target : Prop}, pattern_21_target target → target
theorem prove_pattern_21 : pattern_21_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

