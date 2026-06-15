/- Auto-generated pattern proof file.
   Pattern: 135
   Hash: c362b37e8ea68259
   Goals: 284
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_135_goalIds : List Nat := [284]
inductive pattern_135_target : Prop → Prop
  | goal_284 : pattern_135_target goal_284_stmt

def pattern_135_stmt : Prop :=
  ∀ {target : Prop}, pattern_135_target target → target
theorem prove_pattern_135 : pattern_135_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

