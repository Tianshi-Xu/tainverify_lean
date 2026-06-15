/- Auto-generated pattern proof file.
   Pattern: 45
   Hash: 644e592295a86185
   Goals: 77, 102
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_45_goalIds : List Nat := [77, 102]
inductive pattern_45_target : Prop → Prop
  | goal_77 : pattern_45_target goal_77_stmt
  | goal_102 : pattern_45_target goal_102_stmt

def pattern_45_stmt : Prop :=
  ∀ {target : Prop}, pattern_45_target target → target
theorem prove_pattern_45 : pattern_45_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

