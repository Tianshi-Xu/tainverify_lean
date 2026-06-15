/- Auto-generated pattern proof file.
   Pattern: 13
   Hash: 9b4b67f479a00332
   Goals: 17
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_13_goalIds : List Nat := [17]
inductive pattern_13_target : Prop → Prop
  | goal_17 : pattern_13_target goal_17_stmt

def pattern_13_stmt : Prop :=
  ∀ {target : Prop}, pattern_13_target target → target
theorem prove_pattern_13 : pattern_13_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

