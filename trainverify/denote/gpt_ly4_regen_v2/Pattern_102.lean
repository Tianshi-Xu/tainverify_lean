/- Auto-generated pattern proof file.
   Pattern: 102
   Hash: 40b269bbbe7f65b4
   Goals: 196
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_102_goalIds : List Nat := [196]
inductive pattern_102_target : Prop → Prop
  | goal_196 : pattern_102_target goal_196_stmt

def pattern_102_stmt : Prop :=
  ∀ {target : Prop}, pattern_102_target target → target
theorem prove_pattern_102 : pattern_102_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

