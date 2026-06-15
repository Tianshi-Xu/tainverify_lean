/- Auto-generated pattern proof file.
   Pattern: 70
   Hash: 86df561567ca4b6b
   Goals: 130
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_70_goalIds : List Nat := [130]
inductive pattern_70_target : Prop → Prop
  | goal_130 : pattern_70_target goal_130_stmt

def pattern_70_stmt : Prop :=
  ∀ {target : Prop}, pattern_70_target target → target
theorem prove_pattern_70 : pattern_70_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

