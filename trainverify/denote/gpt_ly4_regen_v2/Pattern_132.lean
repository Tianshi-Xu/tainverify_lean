/- Auto-generated pattern proof file.
   Pattern: 132
   Hash: ffafe0f7e19884de
   Goals: 275, 303
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_132_goalIds : List Nat := [275, 303]
inductive pattern_132_target : Prop → Prop
  | goal_275 : pattern_132_target goal_275_stmt
  | goal_303 : pattern_132_target goal_303_stmt

def pattern_132_stmt : Prop :=
  ∀ {target : Prop}, pattern_132_target target → target
theorem prove_pattern_132 : pattern_132_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

