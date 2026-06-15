/- Auto-generated pattern proof file.
   Pattern: 62
   Hash: ae3c4abdfbe3fa40
   Goals: 119, 185, 187
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_62_goalIds : List Nat := [119, 185, 187]
inductive pattern_62_target : Prop → Prop
  | goal_119 : pattern_62_target goal_119_stmt
  | goal_185 : pattern_62_target goal_185_stmt
  | goal_187 : pattern_62_target goal_187_stmt

def pattern_62_stmt : Prop :=
  ∀ {target : Prop}, pattern_62_target target → target
theorem prove_pattern_62 : pattern_62_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

