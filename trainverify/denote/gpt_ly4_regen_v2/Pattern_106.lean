/- Auto-generated pattern proof file.
   Pattern: 106
   Hash: 30fb65ed03797256
   Goals: 201
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_106_goalIds : List Nat := [201]
inductive pattern_106_target : Prop → Prop
  | goal_201 : pattern_106_target goal_201_stmt

def pattern_106_stmt : Prop :=
  ∀ {target : Prop}, pattern_106_target target → target
theorem prove_pattern_106 : pattern_106_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

