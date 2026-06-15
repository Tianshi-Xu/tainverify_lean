/- Auto-generated pattern proof file.
   Pattern: 107
   Hash: d94b7f47ea886629
   Goals: 202
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_107_goalIds : List Nat := [202]
inductive pattern_107_target : Prop → Prop
  | goal_202 : pattern_107_target goal_202_stmt

def pattern_107_stmt : Prop :=
  ∀ {target : Prop}, pattern_107_target target → target
theorem prove_pattern_107 : pattern_107_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

