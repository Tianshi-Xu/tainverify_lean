/- Auto-generated pattern proof file.
   Pattern: 111
   Hash: d9043ed40cc1fa08
   Goals: 210, 213, 245, 248
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_111_goalIds : List Nat := [210, 213, 245, 248]
inductive pattern_111_target : Prop → Prop
  | goal_210 : pattern_111_target goal_210_stmt
  | goal_213 : pattern_111_target goal_213_stmt
  | goal_245 : pattern_111_target goal_245_stmt
  | goal_248 : pattern_111_target goal_248_stmt

def pattern_111_stmt : Prop :=
  ∀ {target : Prop}, pattern_111_target target → target
theorem prove_pattern_111 : pattern_111_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

