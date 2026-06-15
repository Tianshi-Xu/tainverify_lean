/- Auto-generated pattern proof file.
   Pattern: 113
   Hash: ada023af4e28eef1
   Goals: 212, 247
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_113_goalIds : List Nat := [212, 247]
inductive pattern_113_target : Prop → Prop
  | goal_212 : pattern_113_target goal_212_stmt
  | goal_247 : pattern_113_target goal_247_stmt

def pattern_113_stmt : Prop :=
  ∀ {target : Prop}, pattern_113_target target → target
theorem prove_pattern_113 : pattern_113_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

