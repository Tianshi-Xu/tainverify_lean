/- Auto-generated pattern proof file.
   Pattern: 154
   Hash: b6e95f2ab8c37f12
   Goals: 429, 569
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_154_goalIds : List Nat := [429, 569]
inductive pattern_154_target : Prop → Prop
  | goal_429 : pattern_154_target goal_429_stmt
  | goal_569 : pattern_154_target goal_569_stmt

def pattern_154_stmt : Prop :=
  ∀ {target : Prop}, pattern_154_target target → target
theorem prove_pattern_154 : pattern_154_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

