/- Auto-generated pattern proof file.
   Pattern: 19
   Hash: 079c368d91506bb2
   Goals: 23, 26, 51, 53, 106
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_19_goalIds : List Nat := [23, 26, 51, 53, 106]
inductive pattern_19_target : Prop → Prop
  | goal_23 : pattern_19_target goal_23_stmt
  | goal_26 : pattern_19_target goal_26_stmt
  | goal_51 : pattern_19_target goal_51_stmt
  | goal_53 : pattern_19_target goal_53_stmt
  | goal_106 : pattern_19_target goal_106_stmt

def pattern_19_stmt : Prop :=
  ∀ {target : Prop}, pattern_19_target target → target
theorem prove_pattern_19 : pattern_19_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

