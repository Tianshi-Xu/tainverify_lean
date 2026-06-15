/- Auto-generated pattern proof file.
   Pattern: 116
   Hash: 456f011c091cba56
   Goals: 229
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_116_goalIds : List Nat := [229]
inductive pattern_116_target : Prop → Prop
  | goal_229 : pattern_116_target goal_229_stmt

def pattern_116_stmt : Prop :=
  ∀ {target : Prop}, pattern_116_target target → target
theorem prove_pattern_116 : pattern_116_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

