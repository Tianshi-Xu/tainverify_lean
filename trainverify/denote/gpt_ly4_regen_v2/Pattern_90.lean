/- Auto-generated pattern proof file.
   Pattern: 90
   Hash: d2e2a2bd15b78ef5
   Goals: 164, 199
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_90_goalIds : List Nat := [164, 199]
inductive pattern_90_target : Prop → Prop
  | goal_164 : pattern_90_target goal_164_stmt
  | goal_199 : pattern_90_target goal_199_stmt

def pattern_90_stmt : Prop :=
  ∀ {target : Prop}, pattern_90_target target → target
theorem prove_pattern_90 : pattern_90_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

