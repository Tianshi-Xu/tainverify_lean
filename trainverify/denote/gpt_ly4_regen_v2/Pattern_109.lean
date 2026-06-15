/- Auto-generated pattern proof file.
   Pattern: 109
   Hash: fd13fb88f22bfeb3
   Goals: 205, 240
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_109_goalIds : List Nat := [205, 240]
inductive pattern_109_target : Prop → Prop
  | goal_205 : pattern_109_target goal_205_stmt
  | goal_240 : pattern_109_target goal_240_stmt

def pattern_109_stmt : Prop :=
  ∀ {target : Prop}, pattern_109_target target → target
theorem prove_pattern_109 : pattern_109_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

