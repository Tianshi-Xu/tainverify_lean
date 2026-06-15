/- Auto-generated pattern proof file.
   Pattern: 72
   Hash: 34487127b05a0eac
   Goals: 132
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_72_goalIds : List Nat := [132]
inductive pattern_72_target : Prop → Prop
  | goal_132 : pattern_72_target goal_132_stmt

def pattern_72_stmt : Prop :=
  ∀ {target : Prop}, pattern_72_target target → target
theorem prove_pattern_72 : pattern_72_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

