/- Auto-generated pattern proof file.
   Pattern: 42
   Hash: 636e2544da31dfa4
   Goals: 73, 98
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_42_goalIds : List Nat := [73, 98]
inductive pattern_42_target : Prop → Prop
  | goal_73 : pattern_42_target goal_73_stmt
  | goal_98 : pattern_42_target goal_98_stmt

def pattern_42_stmt : Prop :=
  ∀ {target : Prop}, pattern_42_target target → target
theorem prove_pattern_42 : pattern_42_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

