/- Auto-generated pattern proof file.
   Pattern: 134
   Hash: 03d3dfbf604868f7
   Goals: 283
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_134_goalIds : List Nat := [283]
inductive pattern_134_target : Prop → Prop
  | goal_283 : pattern_134_target goal_283_stmt

def pattern_134_stmt : Prop :=
  ∀ {target : Prop}, pattern_134_target target → target
theorem prove_pattern_134 : pattern_134_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

