/- Auto-generated pattern proof file.
   Pattern: 131
   Hash: 574af4a3647d8990
   Goals: 270, 274
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_131_goalIds : List Nat := [270, 274]
inductive pattern_131_target : Prop → Prop
  | goal_270 : pattern_131_target goal_270_stmt
  | goal_274 : pattern_131_target goal_274_stmt

def pattern_131_stmt : Prop :=
  ∀ {target : Prop}, pattern_131_target target → target
theorem prove_pattern_131 : pattern_131_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

