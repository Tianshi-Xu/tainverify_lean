/- Auto-generated pattern proof file.
   Pattern: 89
   Hash: 761c1162b2c1655d
   Goals: 163, 233
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_89_goalIds : List Nat := [163, 233]
inductive pattern_89_target : Prop → Prop
  | goal_163 : pattern_89_target goal_163_stmt
  | goal_233 : pattern_89_target goal_233_stmt

def pattern_89_stmt : Prop :=
  ∀ {target : Prop}, pattern_89_target target → target
theorem prove_pattern_89 : pattern_89_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

