/- Auto-generated pattern proof file.
   Pattern: 165
   Hash: a91459563957c507
   Goals: 470, 497, 610
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_165_goalIds : List Nat := [470, 497, 610]
inductive pattern_165_target : Prop → Prop
  | goal_470 : pattern_165_target goal_470_stmt
  | goal_497 : pattern_165_target goal_497_stmt
  | goal_610 : pattern_165_target goal_610_stmt

def pattern_165_stmt : Prop :=
  ∀ {target : Prop}, pattern_165_target target → target
theorem prove_pattern_165 : pattern_165_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

