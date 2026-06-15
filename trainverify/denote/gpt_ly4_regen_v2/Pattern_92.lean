/- Auto-generated pattern proof file.
   Pattern: 92
   Hash: 51204b71ee497838
   Goals: 167
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_92_goalIds : List Nat := [167]
inductive pattern_92_target : Prop → Prop
  | goal_167 : pattern_92_target goal_167_stmt

def pattern_92_stmt : Prop :=
  ∀ {target : Prop}, pattern_92_target target → target
theorem prove_pattern_92 : pattern_92_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

