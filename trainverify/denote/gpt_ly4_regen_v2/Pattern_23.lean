/- Auto-generated pattern proof file.
   Pattern: 23
   Hash: af0033c84cdc4624
   Goals: 28
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_23_goalIds : List Nat := [28]
inductive pattern_23_target : Prop → Prop
  | goal_28 : pattern_23_target goal_28_stmt

def pattern_23_stmt : Prop :=
  ∀ {target : Prop}, pattern_23_target target → target
theorem prove_pattern_23 : pattern_23_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

