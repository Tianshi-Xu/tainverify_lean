/- Auto-generated pattern proof file.
   Pattern: 26
   Hash: 8bc48b286bacd2f6
   Goals: 35, 64, 89
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_26_goalIds : List Nat := [35, 64, 89]
inductive pattern_26_target : Prop → Prop
  | goal_35 : pattern_26_target goal_35_stmt
  | goal_64 : pattern_26_target goal_64_stmt
  | goal_89 : pattern_26_target goal_89_stmt

def pattern_26_stmt : Prop :=
  ∀ {target : Prop}, pattern_26_target target → target
theorem prove_pattern_26 : pattern_26_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

