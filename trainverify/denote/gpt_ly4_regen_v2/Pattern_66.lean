/- Auto-generated pattern proof file.
   Pattern: 66
   Hash: cda56fc9aa771339
   Goals: 124
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_66_goalIds : List Nat := [124]
inductive pattern_66_target : Prop → Prop
  | goal_124 : pattern_66_target goal_124_stmt

def pattern_66_stmt : Prop :=
  ∀ {target : Prop}, pattern_66_target target → target
theorem prove_pattern_66 : pattern_66_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

