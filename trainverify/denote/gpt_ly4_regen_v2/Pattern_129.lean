/- Auto-generated pattern proof file.
   Pattern: 129
   Hash: cd4c1af3aff22a92
   Goals: 265
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_129_goalIds : List Nat := [265]
inductive pattern_129_target : Prop → Prop
  | goal_265 : pattern_129_target goal_265_stmt

def pattern_129_stmt : Prop :=
  ∀ {target : Prop}, pattern_129_target target → target
theorem prove_pattern_129 : pattern_129_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

