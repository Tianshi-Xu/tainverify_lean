/- Auto-generated pattern proof file.
   Pattern: 124
   Hash: ef160eacb7218322
   Goals: 256
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_124_goalIds : List Nat := [256]
inductive pattern_124_target : Prop → Prop
  | goal_256 : pattern_124_target goal_256_stmt

def pattern_124_stmt : Prop :=
  ∀ {target : Prop}, pattern_124_target target → target
theorem prove_pattern_124 : pattern_124_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

