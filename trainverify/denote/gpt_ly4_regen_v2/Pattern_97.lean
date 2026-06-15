/- Auto-generated pattern proof file.
   Pattern: 97
   Hash: 95f2c914115b6f2c
   Goals: 180
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_97_goalIds : List Nat := [180]
inductive pattern_97_target : Prop → Prop
  | goal_180 : pattern_97_target goal_180_stmt

def pattern_97_stmt : Prop :=
  ∀ {target : Prop}, pattern_97_target target → target
theorem prove_pattern_97 : pattern_97_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

