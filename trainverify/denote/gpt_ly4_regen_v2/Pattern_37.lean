/- Auto-generated pattern proof file.
   Pattern: 37
   Hash: 219033270fed5ec2
   Goals: 66
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_37_goalIds : List Nat := [66]
inductive pattern_37_target : Prop → Prop
  | goal_66 : pattern_37_target goal_66_stmt

def pattern_37_stmt : Prop :=
  ∀ {target : Prop}, pattern_37_target target → target
theorem prove_pattern_37 : pattern_37_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

