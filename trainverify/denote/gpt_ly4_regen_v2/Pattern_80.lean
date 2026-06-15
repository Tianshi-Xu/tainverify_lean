/- Auto-generated pattern proof file.
   Pattern: 80
   Hash: 167f5f740a7f0b4e
   Goals: 144
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_80_goalIds : List Nat := [144]
inductive pattern_80_target : Prop → Prop
  | goal_144 : pattern_80_target goal_144_stmt

def pattern_80_stmt : Prop :=
  ∀ {target : Prop}, pattern_80_target target → target
theorem prove_pattern_80 : pattern_80_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

