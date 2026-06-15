/- Auto-generated pattern proof file.
   Pattern: 74
   Hash: d8751f17a8d75fdc
   Goals: 134
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_74_goalIds : List Nat := [134]
inductive pattern_74_target : Prop → Prop
  | goal_134 : pattern_74_target goal_134_stmt

def pattern_74_stmt : Prop :=
  ∀ {target : Prop}, pattern_74_target target → target
theorem prove_pattern_74 : pattern_74_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

