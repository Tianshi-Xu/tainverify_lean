/- Auto-generated pattern proof file.
   Pattern: 118
   Hash: 3e39672b4e06ee3a
   Goals: 232
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_118_goalIds : List Nat := [232]
inductive pattern_118_target : Prop → Prop
  | goal_232 : pattern_118_target goal_232_stmt

def pattern_118_stmt : Prop :=
  ∀ {target : Prop}, pattern_118_target target → target
theorem prove_pattern_118 : pattern_118_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

