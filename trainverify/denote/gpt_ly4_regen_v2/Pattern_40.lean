/- Auto-generated pattern proof file.
   Pattern: 40
   Hash: cdd25357f2008c40
   Goals: 70
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_40_goalIds : List Nat := [70]
inductive pattern_40_target : Prop → Prop
  | goal_70 : pattern_40_target goal_70_stmt

def pattern_40_stmt : Prop :=
  ∀ {target : Prop}, pattern_40_target target → target
theorem prove_pattern_40 : pattern_40_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

