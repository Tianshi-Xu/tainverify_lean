/- Auto-generated pattern proof file.
   Pattern: 93
   Hash: 5693f5d6954802d2
   Goals: 169
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_93_goalIds : List Nat := [169]
inductive pattern_93_target : Prop → Prop
  | goal_169 : pattern_93_target goal_169_stmt

def pattern_93_stmt : Prop :=
  ∀ {target : Prop}, pattern_93_target target → target
theorem prove_pattern_93 : pattern_93_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

