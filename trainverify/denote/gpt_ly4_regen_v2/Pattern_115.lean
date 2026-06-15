/- Auto-generated pattern proof file.
   Pattern: 115
   Hash: 5ee1d6a502ef74c1
   Goals: 227
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_115_goalIds : List Nat := [227]
inductive pattern_115_target : Prop → Prop
  | goal_227 : pattern_115_target goal_227_stmt

def pattern_115_stmt : Prop :=
  ∀ {target : Prop}, pattern_115_target target → target
theorem prove_pattern_115 : pattern_115_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

