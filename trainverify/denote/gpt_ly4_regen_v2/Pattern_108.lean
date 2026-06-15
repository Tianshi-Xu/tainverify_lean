/- Auto-generated pattern proof file.
   Pattern: 108
   Hash: b932491bee1c0daf
   Goals: 204, 239
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_108_goalIds : List Nat := [204, 239]
inductive pattern_108_target : Prop → Prop
  | goal_204 : pattern_108_target goal_204_stmt
  | goal_239 : pattern_108_target goal_239_stmt

def pattern_108_stmt : Prop :=
  ∀ {target : Prop}, pattern_108_target target → target
theorem prove_pattern_108 : pattern_108_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

