/- Auto-generated pattern proof file.
   Pattern: 91
   Hash: 34241163dc5a44dc
   Goals: 165
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_91_goalIds : List Nat := [165]
inductive pattern_91_target : Prop → Prop
  | goal_165 : pattern_91_target goal_165_stmt

def pattern_91_stmt : Prop :=
  ∀ {target : Prop}, pattern_91_target target → target
theorem prove_pattern_91 : pattern_91_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

