/- Auto-generated pattern proof file.
   Pattern: 28
   Hash: bb72061ee5790bea
   Goals: 41
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_28_goalIds : List Nat := [41]
inductive pattern_28_target : Prop → Prop
  | goal_41 : pattern_28_target goal_41_stmt

def pattern_28_stmt : Prop :=
  ∀ {target : Prop}, pattern_28_target target → target
theorem prove_pattern_28 : pattern_28_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

