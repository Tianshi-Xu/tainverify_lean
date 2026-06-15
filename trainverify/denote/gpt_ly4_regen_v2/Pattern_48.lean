/- Auto-generated pattern proof file.
   Pattern: 48
   Hash: 9bd201aef66ba58a
   Goals: 93
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_48_goalIds : List Nat := [93]
inductive pattern_48_target : Prop → Prop
  | goal_93 : pattern_48_target goal_93_stmt

def pattern_48_stmt : Prop :=
  ∀ {target : Prop}, pattern_48_target target → target
theorem prove_pattern_48 : pattern_48_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

