/- Auto-generated pattern proof file.
   Pattern: 65
   Hash: 80e110f2357c8703
   Goals: 123, 158, 191, 226
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_65_goalIds : List Nat := [123, 158, 191, 226]
inductive pattern_65_target : Prop → Prop
  | goal_123 : pattern_65_target goal_123_stmt
  | goal_158 : pattern_65_target goal_158_stmt
  | goal_191 : pattern_65_target goal_191_stmt
  | goal_226 : pattern_65_target goal_226_stmt

def pattern_65_stmt : Prop :=
  ∀ {target : Prop}, pattern_65_target target → target
theorem prove_pattern_65 : pattern_65_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

