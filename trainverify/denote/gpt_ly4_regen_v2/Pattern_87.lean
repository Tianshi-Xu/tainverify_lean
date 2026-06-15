/- Auto-generated pattern proof file.
   Pattern: 87
   Hash: e6b8c95f73a8e1d1
   Goals: 161
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_87_goalIds : List Nat := [161]
inductive pattern_87_target : Prop → Prop
  | goal_161 : pattern_87_target goal_161_stmt

def pattern_87_stmt : Prop :=
  ∀ {target : Prop}, pattern_87_target target → target
theorem prove_pattern_87 : pattern_87_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

