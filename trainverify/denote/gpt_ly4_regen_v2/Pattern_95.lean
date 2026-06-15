/- Auto-generated pattern proof file.
   Pattern: 95
   Hash: 8d1a9cc8149f809c
   Goals: 172
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_95_goalIds : List Nat := [172]
inductive pattern_95_target : Prop → Prop
  | goal_172 : pattern_95_target goal_172_stmt

def pattern_95_stmt : Prop :=
  ∀ {target : Prop}, pattern_95_target target → target
theorem prove_pattern_95 : pattern_95_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

