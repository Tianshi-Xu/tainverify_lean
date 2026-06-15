/- Auto-generated pattern proof file.
   Pattern: 36
   Hash: e5d4d61eeb799187
   Goals: 65
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_36_goalIds : List Nat := [65]
inductive pattern_36_target : Prop → Prop
  | goal_65 : pattern_36_target goal_65_stmt

def pattern_36_stmt : Prop :=
  ∀ {target : Prop}, pattern_36_target target → target
theorem prove_pattern_36 : pattern_36_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

