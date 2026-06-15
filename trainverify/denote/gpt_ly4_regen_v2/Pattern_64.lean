/- Auto-generated pattern proof file.
   Pattern: 64
   Hash: 3b0c900681d51648
   Goals: 122, 127
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_64_goalIds : List Nat := [122, 127]
inductive pattern_64_target : Prop → Prop
  | goal_122 : pattern_64_target goal_122_stmt
  | goal_127 : pattern_64_target goal_127_stmt

def pattern_64_stmt : Prop :=
  ∀ {target : Prop}, pattern_64_target target → target
theorem prove_pattern_64 : pattern_64_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

