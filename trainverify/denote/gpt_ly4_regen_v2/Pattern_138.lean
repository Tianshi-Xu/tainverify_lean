/- Auto-generated pattern proof file.
   Pattern: 138
   Hash: 35b9a84bfd883df5
   Goals: 291
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_138_goalIds : List Nat := [291]
inductive pattern_138_target : Prop → Prop
  | goal_291 : pattern_138_target goal_291_stmt

def pattern_138_stmt : Prop :=
  ∀ {target : Prop}, pattern_138_target target → target
theorem prove_pattern_138 : pattern_138_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

