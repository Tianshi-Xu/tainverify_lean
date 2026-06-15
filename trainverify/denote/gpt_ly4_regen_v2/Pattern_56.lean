/- Auto-generated pattern proof file.
   Pattern: 56
   Hash: c559d8bbd9f49644
   Goals: 111, 137, 146
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_56_goalIds : List Nat := [111, 137, 146]
inductive pattern_56_target : Prop → Prop
  | goal_111 : pattern_56_target goal_111_stmt
  | goal_137 : pattern_56_target goal_137_stmt
  | goal_146 : pattern_56_target goal_146_stmt

def pattern_56_stmt : Prop :=
  ∀ {target : Prop}, pattern_56_target target → target
theorem prove_pattern_56 : pattern_56_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

