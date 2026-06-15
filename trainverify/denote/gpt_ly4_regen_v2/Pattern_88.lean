/- Auto-generated pattern proof file.
   Pattern: 88
   Hash: 6b95716eb7c33403
   Goals: 162
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_88_goalIds : List Nat := [162]
inductive pattern_88_target : Prop → Prop
  | goal_162 : pattern_88_target goal_162_stmt

def pattern_88_stmt : Prop :=
  ∀ {target : Prop}, pattern_88_target target → target
theorem prove_pattern_88 : pattern_88_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

