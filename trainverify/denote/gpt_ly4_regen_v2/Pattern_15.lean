/- Auto-generated pattern proof file.
   Pattern: 15
   Hash: e5e3b810aabecab2
   Goals: 19
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_15_goalIds : List Nat := [19]
inductive pattern_15_target : Prop → Prop
  | goal_19 : pattern_15_target goal_19_stmt

def pattern_15_stmt : Prop :=
  ∀ {target : Prop}, pattern_15_target target → target
theorem prove_pattern_15 : pattern_15_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

