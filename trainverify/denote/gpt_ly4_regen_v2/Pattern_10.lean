/- Auto-generated pattern proof file.
   Pattern: 10
   Hash: 6f2128dfb677e726
   Goals: 12, 37, 60, 85
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_10_goalIds : List Nat := [12, 37, 60, 85]
inductive pattern_10_target : Prop → Prop
  | goal_12 : pattern_10_target goal_12_stmt
  | goal_37 : pattern_10_target goal_37_stmt
  | goal_60 : pattern_10_target goal_60_stmt
  | goal_85 : pattern_10_target goal_85_stmt

def pattern_10_stmt : Prop :=
  ∀ {target : Prop}, pattern_10_target target → target
theorem prove_pattern_10 : pattern_10_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

