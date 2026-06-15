/- Auto-generated pattern proof file.
   Pattern: 21
   Hash: 0c671a7b0d6e6d62
   Goals: 25, 50, 105
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_21_goalIds : List Nat := [25, 50, 105]
inductive pattern_21_target : Prop → Prop
  | goal_25 : pattern_21_target goal_25_stmt
  | goal_50 : pattern_21_target goal_50_stmt
  | goal_105 : pattern_21_target goal_105_stmt

def pattern_21_stmt : Prop :=
  ∀ {target : Prop}, pattern_21_target target → target
theorem prove_pattern_21 : pattern_21_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

