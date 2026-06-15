/- Auto-generated pattern proof file.
   Pattern: 81
   Hash: 68d18d46c3e174f2
   Goals: 145, 171
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_81_goalIds : List Nat := [145, 171]
inductive pattern_81_target : Prop → Prop
  | goal_145 : pattern_81_target goal_145_stmt
  | goal_171 : pattern_81_target goal_171_stmt

def pattern_81_stmt : Prop :=
  ∀ {target : Prop}, pattern_81_target target → target
theorem prove_pattern_81 : pattern_81_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

