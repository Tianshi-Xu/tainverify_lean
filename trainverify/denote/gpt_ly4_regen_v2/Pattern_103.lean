/- Auto-generated pattern proof file.
   Pattern: 103
   Hash: dc9e058cbda65265
   Goals: 197
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_103_goalIds : List Nat := [197]
inductive pattern_103_target : Prop → Prop
  | goal_197 : pattern_103_target goal_197_stmt

def pattern_103_stmt : Prop :=
  ∀ {target : Prop}, pattern_103_target target → target
theorem prove_pattern_103 : pattern_103_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

