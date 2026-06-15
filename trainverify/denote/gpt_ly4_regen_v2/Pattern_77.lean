/- Auto-generated pattern proof file.
   Pattern: 77
   Hash: 2c9154fd373a643c
   Goals: 140, 175, 178, 254
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_77_goalIds : List Nat := [140, 175, 178, 254]
inductive pattern_77_target : Prop → Prop
  | goal_140 : pattern_77_target goal_140_stmt
  | goal_175 : pattern_77_target goal_175_stmt
  | goal_178 : pattern_77_target goal_178_stmt
  | goal_254 : pattern_77_target goal_254_stmt

def pattern_77_stmt : Prop :=
  ∀ {target : Prop}, pattern_77_target target → target
theorem prove_pattern_77 : pattern_77_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

