/- Auto-generated pattern proof file.
   Pattern: 7
   Hash: b9a1e6b010ffbff2
   Goals: 8, 56, 57
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_7_goalIds : List Nat := [8, 56, 57]
inductive pattern_7_target : Prop → Prop
  | goal_8 : pattern_7_target goal_8_stmt
  | goal_56 : pattern_7_target goal_56_stmt
  | goal_57 : pattern_7_target goal_57_stmt

def pattern_7_stmt : Prop :=
  ∀ {target : Prop}, pattern_7_target target → target
theorem prove_pattern_7 : pattern_7_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

