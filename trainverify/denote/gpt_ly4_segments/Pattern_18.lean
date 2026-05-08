/- Auto-generated pattern proof file.
   Pattern: 18
   Hash: 6196320c66d11fc4
   Goals: 22, 47, 72, 97
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_18_goalIds : List Nat := [22, 47, 72, 97]
inductive pattern_18_target : Prop → Prop
  | goal_22 : pattern_18_target goal_22_stmt
  | goal_47 : pattern_18_target goal_47_stmt
  | goal_72 : pattern_18_target goal_72_stmt
  | goal_97 : pattern_18_target goal_97_stmt

def pattern_18_stmt : Prop :=
  ∀ {target : Prop}, pattern_18_target target → target
theorem prove_pattern_18 : pattern_18_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

